# ruff: noqa
from __future__ import annotations

r"""
Gerador de Áudio (Mota Midia) — arquivo único

ENTRADA por linha (START e END por frase):
  HH:MM:SS:FF --> HH:MM:SS:FF Texto da frase...

FPS / timecode:
- Aceita 30fps (FF 00–29) e 60fps (FF 00–59).
- Auto-detect:
    se qualquer FF >= 30 -> assume 60fps
    senão -> assume 30fps
- Override opcional no topo do texto:
    FPS=60  (ou FPS:60)  /  FPS=30 (ou FPS:30)

MODOS (2 padrões):
1) Padrão (Fit):
   - 1 chamada TTS por frase (ElevenLabs /with-timestamps), sempre speed=1.0.
   - Pós-processamento local:
       * Sempre remove silêncio no INÍCIO e no FIM (trim seguro).
       * Áudio pequeno: pode desacelerar até 90% (0.90), sem comprimir pausas internas.
       * Áudio grande: (1) tenta acelerar até 120% sem compressão,
                      (2) comprime silêncios internos e tenta até 120%,
                      (3) se ainda não couber, acelera >120% o quanto precisar (com cap de segurança).
2) Padrão YouTube:
   - 1 chamada TTS por frase, sempre speed=1.0.
   - Se o áudio couber na janela START/END: NÃO mexe em nada (fica exatamente como vem do ElevenLabs).
   - Só se NÃO couber: corta silêncios (bordas + internos) para tentar encaixar.
   - Nunca altera velocidade.
   - Se ainda não couber: mantém overflow (sem cortar palavras) e avisa.

Presets de voz por aba:
- VOICE_PRESETS_BY_TAB: preenche automaticamente a voz de cada aba (T1..T6).
- Aplica ao criar aba e ao carregar vozes/trocar de conta.

Exportação:
- Menu ☰ -> "Exportar textos de todas as abas": salva 1 arquivo .txt por aba automaticamente.

Requisitos:
  pip install ttkbootstrap pydub pygame requests
  (pydub requer ffmpeg disponível no PATH para mp3)
"""

import base64
import io
import json
import logging
import os
import re
import subprocess
import tempfile
import threading
import warnings
from dataclasses import dataclass
from logging.handlers import RotatingFileHandler
from queue import Empty, Queue
from typing import Any, Dict, List, Optional, Tuple

import requests
import ttkbootstrap as ttkb
from pydub import AudioSegment
from pydub.silence import detect_nonsilent
from tkinter import END, StringVar, filedialog, messagebox, simpledialog
from tkinter import ttk

# Som de notificação (opcional)
try:
    from pygame import mixer  # type: ignore

    PYGAME_AVAILABLE = True
except Exception:
    mixer = None
    PYGAME_AVAILABLE = False

warnings.filterwarnings("ignore", category=UserWarning, message="FP16 is not supported on CPU")


# -----------------------------
# Paths / Storage / Logging
# -----------------------------


def _appdata_dir() -> str:
    base = os.getenv("APPDATA") or os.path.expanduser("~")
    path = os.path.join(base, "MotApp")
    os.makedirs(path, exist_ok=True)
    return path

import webbrowser
from packaging.version import Version  # pip install packaging

APP_VERSION = "1.0.0"
GITHUB_OWNER = "SEU_USUARIO"
GITHUB_REPO = "SEU_REPO"
INSTALLER_NAME_PREFIX = "MotApp_Setup_"  # seus assets devem seguir isso

APP_DIR = _appdata_dir()
LOG_FILE = os.path.join(APP_DIR, "app.log")
CONFIG_FILE = os.path.join(APP_DIR, "config.json")
API_KEYS_FILE = os.path.join(APP_DIR, "api_keys.json")
NOTIFICATION_SOUND_FILE = os.path.join(APP_DIR, "notification_sound.json")


def setup_logging() -> logging.Logger:
    lg = logging.getLogger("motapp")
    lg.setLevel(logging.DEBUG)

    if not lg.handlers:
        handler = RotatingFileHandler(LOG_FILE, maxBytes=2_000_000, backupCount=5, encoding="utf-8")
        fmt = logging.Formatter("%(asctime)s [%(levelname)s] %(threadName)s %(name)s: %(message)s")
        handler.setFormatter(fmt)
        lg.addHandler(handler)

    return lg


logger = setup_logging()


def excepthook(exc_type, exc, tb):
    logger.exception("Exceção não tratada", exc_info=(exc_type, exc, tb))


import sys  # noqa: E402

sys.excepthook = excepthook


# -----------------------------
# Config Stores
# -----------------------------


class ConfigStore:
    def __init__(self, path: str):
        self.path = path

    def load(self) -> Dict[str, Any]:
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                data = json.load(f)
                return data if isinstance(data, dict) else {"tema": "darkly", "ultima_conta": "", "audio_mode": "padrao"}
        except (FileNotFoundError, json.JSONDecodeError):
            return {"tema": "darkly", "ultima_conta": "", "audio_mode": "padrao"}

    def save(self, config: Dict[str, Any]) -> None:
        with open(self.path, "w", encoding="utf-8") as f:
            json.dump(config, f, ensure_ascii=False, indent=2)


class NotificationSoundStore:
    def __init__(self, path: str):
        self.path = path

    def load(self) -> Dict[str, Any]:
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if not isinstance(data, dict):
                return {"caminho_som": None}
            return {"caminho_som": data.get("caminho_som")}
        except (FileNotFoundError, json.JSONDecodeError):
            return {"caminho_som": None}

    def save(self, caminho_som: Optional[str]) -> None:
        with open(self.path, "w", encoding="utf-8") as f:
            json.dump({"caminho_som": caminho_som}, f, ensure_ascii=False, indent=2)


class ApiKeyStore:
    """
    Armazena chaves em JSON no AppData.
    Se quiser maior segurança, pode trocar por keyring/Credential Manager.
    """

    def __init__(self, path: str):
        self.path = path
        if not os.path.exists(self.path):
            self.save({})

    def load(self) -> Dict[str, str]:
        try:
            with open(self.path, "r", encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except (FileNotFoundError, json.JSONDecodeError):
            return {}

    def save(self, data: Dict[str, str]) -> None:
        with open(self.path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)


# -----------------------------
# ElevenLabs Client
# -----------------------------


@dataclass
class ElevenUserQuota:
    valid: bool
    character_limit: int = 0
    character_count: int = 0
    error: Optional[str] = None


@dataclass
class TtsWithTimingResult:
    mp3_bytes: bytes
    speech_start_seconds: Optional[float]
    speech_end_seconds: Optional[float]


class ElevenLabsClient:
    BASE = "https://api.elevenlabs.io/v1"

    def __init__(self):
        self.session = requests.Session()

    def get_user_quota(self, api_key: str, timeout: Tuple[int, int] = (5, 15)) -> ElevenUserQuota:
        url = f"{self.BASE}/user"
        headers = {"xi-api-key": api_key}
        try:
            r = self.session.get(url, headers=headers, timeout=timeout)
            if r.status_code == 401:
                return ElevenUserQuota(valid=False, error="Chave de API inválida ou não autorizada.")
            r.raise_for_status()
            data = r.json()
            sub = data.get("subscription", {}) if isinstance(data, dict) else {}
            return ElevenUserQuota(
                valid=True,
                character_limit=int(sub.get("character_limit", 0) or 0),
                character_count=int(sub.get("character_count", 0) or 0),
            )
        except requests.exceptions.RequestException as e:
            logger.exception("Falha ao obter quota do usuário")
            return ElevenUserQuota(valid=False, error=f"Erro ao consultar usuário: {e}")

    def list_voices(self, api_key: str, timeout: Tuple[int, int] = (5, 15)) -> List[Dict[str, Any]]:
        url = f"{self.BASE}/voices"
        headers = {"xi-api-key": api_key}
        r = self.session.get(url, headers=headers, timeout=timeout)
        r.raise_for_status()
        data = r.json()
        voices = data.get("voices", []) if isinstance(data, dict) else []
        return voices if isinstance(voices, list) else []

    def tts_with_timestamps(
        self,
        api_key: str,
        voice_id: str,
        text: str,
        stability: float,
        similarity_boost: float,
        style_exaggeration: float,
        speed: float,
        model_id: str = "eleven_multilingual_v2",
        timeout: Tuple[int, int] = (5, 30),
    ) -> TtsWithTimingResult:
        url = f"{self.BASE}/text-to-speech/{voice_id}/with-timestamps"
        headers = {
            "xi-api-key": api_key,
            "Content-Type": "application/json",
            "Accept": "application/json",
        }
        payload = {
            "text": text,
            "model_id": model_id,
            "voice_settings": {
                "stability": stability,
                "similarity_boost": similarity_boost,
                "style_exaggeration": style_exaggeration,
                "speed": float(speed),
            },
        }

        r = self.session.post(url, headers=headers, json=payload, timeout=timeout)
        r.raise_for_status()
        data = r.json() if r.content else {}
        if not isinstance(data, dict):
            raise ValueError("Resposta inesperada da API (não é objeto JSON).")

        audio_b64 = data.get("audio_base64")
        if not audio_b64:
            raise ValueError("Resposta da API não contém 'audio_base64'.")

        mp3_bytes = base64.b64decode(audio_b64)

        align = data.get("normalized_alignment") or data.get("alignment") or {}
        speech_start = None
        speech_end = None
        if isinstance(align, dict):
            starts = align.get("character_start_times_seconds")
            ends = align.get("character_end_times_seconds")
            if isinstance(starts, list) and starts:
                try:
                    speech_start = float(starts[0])
                except Exception:
                    speech_start = None
            if isinstance(ends, list) and ends:
                try:
                    speech_end = float(ends[-1])
                except Exception:
                    speech_end = None

        return TtsWithTimingResult(mp3_bytes=mp3_bytes, speech_start_seconds=speech_start, speech_end_seconds=speech_end)


# -----------------------------
# Timecode parsing / validation (HH:MM:SS:FF --> HH:MM:SS:FF)
# -----------------------------

_LINE_RE = re.compile(
    r"^(?P<h1>\d{2}):(?P<m1>\d{2}):(?P<s1>\d{2}):(?P<f1>\d{2})\s*-->\s*"
    r"(?P<h2>\d{2}):(?P<m2>\d{2}):(?P<s2>\d{2}):(?P<f2>\d{2})\s+"
    r"(?P<text>.+)$"
)
_FPS_DIRECTIVE_RE = re.compile(r"^\s*FPS\s*[:=]\s*(?P<fps>\d+)\s*$", re.IGNORECASE)


def tc_to_ms(h: int, m: int, s: int, f: int, fps: int) -> int:
    fps = 60 if int(fps) == 60 else 30
    return ((h * 3600 + m * 60 + s) * 1000) + int((f * 1000) / fps)


def _extract_fps_directive(lines: List[str]) -> Tuple[Optional[int], List[str]]:
    out: List[str] = []
    fps: Optional[int] = None
    for line in lines:
        m = _FPS_DIRECTIVE_RE.match(line.strip())
        if m and fps is None:
            try:
                v = int(m.group("fps"))
                if v in (30, 60):
                    fps = v
                    continue
            except Exception:
                pass
        out.append(line)
    return fps, out


def _autodetect_fps_from_timecodes(lines: List[str]) -> int:
    max_frame = 0
    for line in lines:
        line = line.strip()
        if not line:
            continue
        m = _LINE_RE.match(line)
        if not m:
            continue
        try:
            f1 = int(m.group("f1"))
            f2 = int(m.group("f2"))
            max_frame = max(max_frame, f1, f2)
        except Exception:
            continue
    return 60 if max_frame >= 30 else 30


def _fps_autodetect_suspicious_warning(lines: List[str]) -> Optional[str]:
    high = 0
    low = 0
    for line in lines:
        m = _LINE_RE.match(line.strip())
        if not m:
            continue
        try:
            f1 = int(m.group("f1"))
            f2 = int(m.group("f2"))
            if max(f1, f2) >= 30:
                high += 1
            else:
                low += 1
        except Exception:
            continue
    if high == 1 and low >= 5:
        return "FPS autodetect=60fps por 1 linha com FF>=30. Confira se não foi erro de frame (digitação)."
    return None


def validate_and_parse_lines(raw: str) -> Tuple[bool, str, List[int], List[int], List[str], List[str]]:
    lines0 = raw.splitlines()
    fps_override, lines = _extract_fps_directive(lines0)
    fps = fps_override if fps_override in (30, 60) else _autodetect_fps_from_timecodes(lines)

    starts: List[int] = []
    ends: List[int] = []
    texts: List[str] = []
    warn: List[str] = []

    for idx, line in enumerate(lines, start=1):
        line = line.strip()
        if not line:
            continue

        m = _LINE_RE.match(line)
        if not m:
            return (
                False,
                f"Formato inválido na linha {idx}:\n{line}\n\n"
                "Use o formato:\n"
                "HH:MM:SS:FF --> HH:MM:SS:FF Texto\n\n"
                "Opcional: inclua uma linha 'FPS=60' no topo para forçar 60fps.",
                [],
                [],
                [],
                [],
            )

        h1, m1, s1, f1 = int(m.group("h1")), int(m.group("m1")), int(m.group("s1")), int(m.group("f1"))
        h2, m2, s2, f2 = int(m.group("h2")), int(m.group("m2")), int(m.group("s2")), int(m.group("f2"))
        text = m.group("text").strip()

        frame_hi = fps - 1
        for (label, vv, lo, hi) in [
            ("minutos", m1, 0, 59),
            ("minutos", m2, 0, 59),
            ("segundos", s1, 0, 59),
            ("segundos", s2, 0, 59),
            ("frames", f1, 0, frame_hi),
            ("frames", f2, 0, frame_hi),
        ]:
            if vv < lo or vv > hi:
                if label == "frames":
                    return (
                        False,
                        f"Frames fora do intervalo na linha {idx}. Para {fps}fps, use FF entre 00 e {frame_hi:02d}.",
                        [],
                        [],
                        [],
                        [],
                    )
                return False, f"{label.capitalize()} fora do intervalo na linha {idx}.", [], [], [], []

        if not text:
            return False, f"Texto vazio na linha {idx}.", [], [], [], []

        start_ms = tc_to_ms(h1, m1, s1, f1, fps)
        end_ms = tc_to_ms(h2, m2, s2, f2, fps)

        if end_ms < start_ms:
            return False, f"Fim menor que início na linha {idx}.", [], [], [], []
        if end_ms == start_ms:
            warn.append(f"Linha {idx}: início e fim são iguais. Janela 0ms; a frase provavelmente não caberá.")

        starts.append(start_ms)
        ends.append(end_ms)
        texts.append(text)

    last = -1
    for tc in starts:
        if tc < last:
            warn.append("Há STARTs regressivos. O alinhamento será por tempo absoluto, mas o roteiro pode ficar incoerente.")
            break
        last = tc

    if not starts:
        return False, "Nenhuma linha válida foi encontrada.", [], [], [], []

    warn.insert(0, f"FPS detectado/selecionado: {fps}fps")
    if fps_override is None and fps == 60:
        suspicious = _fps_autodetect_suspicious_warning(lines)
        if suspicious:
            warn.append(suspicious)

    return True, "", starts, ends, texts, warn


def count_characters_without_timecodes(raw: str) -> int:
    lines0 = raw.splitlines()
    _, lines = _extract_fps_directive(lines0)
    stripped = "\n".join(lines)
    stripped = re.sub(
        r"^\d{2}:\d{2}:\d{2}:\d{2}\s*-->\s*\d{2}:\d{2}:\d{2}:\d{2}\s*",
        "",
        stripped,
        flags=re.MULTILINE,
    )
    stripped = stripped.replace("\n", "")
    return len(stripped)


# -----------------------------
# UI Models / Events
# -----------------------------


@dataclass
class AudioRecord:
    nome: str
    caminho: str
    status: str


@dataclass
class UiEvent:
    tab_name: str
    kind: str  # 'progress', 'message', 'error', 'done'
    payload: Any = None


# -----------------------------
# Tab UI
# -----------------------------


class TabUI:
    def __init__(self, parent, tab_name: str, app: "App"):
        self.parent = parent
        self.tab_name = tab_name
        self.app = app

        self.cancel_event = threading.Event()
        self.worker_thread: Optional[threading.Thread] = None

        self._build()

    def _build(self) -> None:
        aba = self.parent

        frame_esquerda = ttkb.Frame(aba, padding=10)
        frame_esquerda.pack(side="left", fill="both", expand=True)

        texto_frame = ttkb.Frame(frame_esquerda)
        texto_frame.pack(fill="both", expand=True)

        scrollbar = ttkb.Scrollbar(texto_frame)
        scrollbar.pack(side="right", fill="y")

        self.entrada_texto = ttkb.Text(texto_frame, height=15, wrap="word", yscrollcommand=scrollbar.set, undo=True)
        self.entrada_texto.pack(fill="both", expand=True)
        scrollbar.config(command=self.entrada_texto.yview)

        self.char_count_label = ttkb.Label(frame_esquerda, text="Caracteres usados: 0", bootstyle="info")
        self.char_count_label.pack(anchor="w", pady=(5, 0))

        self.entrada_texto.bind("<KeyRelease>", self._on_text_change)
        self._on_text_change(None)

        frame_direita = ttkb.Frame(aba, padding=10)
        frame_direita.pack(side="right", fill="y")

        self.filtro_voz = StringVar(value="Selecione a voz")
        self.combobox_vozes = ttkb.Combobox(frame_direita, textvariable=self.filtro_voz)
        self.combobox_vozes.pack(fill="x", pady=(10, 5))

        self._set_placeholder_state(True)
        self.combobox_vozes.bind("<FocusIn>", self._on_focus_in_voice)
        self.combobox_vozes.bind("<FocusOut>", self._on_focus_out_voice)
        self.combobox_vozes.bind("<KeyRelease>", self._on_voice_typing)

        botao_atualizar = ttkb.Button(frame_direita, text="Carregar Vozes", command=self.app.load_voices, bootstyle="primary")
        botao_atualizar.pack(fill="x", pady=(5, 10))

        frame_inferior = ttkb.Frame(frame_direita)
        frame_inferior.pack(side="bottom", fill="x", anchor="se", pady=10)

        gerar_button = ttkb.Button(frame_inferior, text="Gerar Áudio", command=self.start_generation, bootstyle="success", padding=5)
        gerar_button.pack(fill="x", pady=(0, 5))

        cancelar_button = ttkb.Button(frame_inferior, text="Cancelar Geração", command=self.cancel_generation, bootstyle="danger", padding=5)
        cancelar_button.pack(fill="x", pady=(0, 5))

        # ✅ substitui o antigo botão de exportar por "Limpar Aba"
        limpar_button = ttkb.Button(frame_inferior, text="Limpar Aba", command=self.clear_tab, bootstyle="warning", padding=5)
        limpar_button.pack(fill="x", pady=(0, 5))

        self.progresso = ttkb.Progressbar(frame_inferior, orient="horizontal", mode="determinate")
        self.progresso.pack(fill="x", pady=(0, 5))

        self.progresso_label = ttkb.Label(frame_inferior, text="Progresso: 0%", style="secondary.TLabel")
        self.progresso_label.pack(anchor="w")

        self.mensagem_label = ttkb.Label(frame_inferior, text="", bootstyle="success")
        self.mensagem_label.pack(anchor="w", pady=(5, 0))

    def _on_text_change(self, _event) -> None:
        raw = self.entrada_texto.get("1.0", "end-1c")
        n = count_characters_without_timecodes(raw)
        self.char_count_label.config(text=f"Caracteres usados: {n}")

    def _set_placeholder_state(self, placeholder: bool) -> None:
        if placeholder:
            if self.filtro_voz.get().strip() == "":
                self.filtro_voz.set("Selecione a voz")
        else:
            if self.filtro_voz.get() == "Selecione a voz":
                self.filtro_voz.set("")

    def _on_focus_in_voice(self, _event) -> None:
        self._set_placeholder_state(False)

    def _on_focus_out_voice(self, _event) -> None:
        if not self.filtro_voz.get().strip():
            self._set_placeholder_state(True)

    def _on_voice_typing(self, _event) -> None:
        filtro = self.filtro_voz.get().lower().strip()
        if filtro == "selecione a voz":
            filtro = ""
        names = [v["name"] for v in self.app.all_voices if filtro in v["name"].lower()]
        self.combobox_vozes["values"] = names

    def refresh_voice_list(self) -> None:
        self.combobox_vozes["values"] = [v["name"] for v in self.app.all_voices]

    def clear_tab(self) -> None:
        if not messagebox.askyesno("Limpar Aba", "Deseja apagar todo o conteúdo desta aba?"):
            return
        try:
            self.entrada_texto.delete("1.0", END)
            self.progresso["value"] = 0
            self.progresso_label.config(text="Progresso: 0%")
            self.mensagem_label.config(text="")
            self.char_count_label.config(text="Caracteres usados: 0")
        except Exception as e:
            logger.exception("Falha ao limpar aba")
            messagebox.showerror("Erro", f"Não foi possível limpar a aba:\n{e}")

    def cancel_generation(self) -> None:
        if self.worker_thread and self.worker_thread.is_alive():
            self.cancel_event.set()
            self.mensagem_label.config(text="Cancelamento solicitado. Aguarde finalizar a requisição atual...")
        else:
            messagebox.showinfo("Cancelamento", "Nenhuma geração ativa nesta aba.")

    def start_generation(self) -> None:
        if self.worker_thread and self.worker_thread.is_alive():
            messagebox.showwarning("Aviso", "Já existe uma geração em andamento nesta aba.")
            return

        api_key = self.app.get_selected_api_key()
        if not api_key:
            messagebox.showerror("Erro", "Nenhuma chave de API selecionada.")
            return

        pasta = filedialog.askdirectory(title="Selecione a pasta para salvar o MP3")
        if not pasta:
            self.mensagem_label.config(text="Pasta de salvamento não selecionada.")
            return

        raw = self.entrada_texto.get("1.0", END)
        ok, err, starts, ends, texts, warns = validate_and_parse_lines(raw)
        if not ok:
            messagebox.showerror("Erro", err)
            return
        if warns:
            messagebox.showwarning("Atenção", "\n".join(warns))

        voz = self.combobox_vozes.get().strip()
        if not voz or voz == "Selecione a voz":
            messagebox.showerror("Erro", "Por favor, selecione uma voz.")
            return

        voice_id = self.app.get_voice_id_by_name(voz)
        if not voice_id:
            messagebox.showerror("Erro", f"Voz '{voz}' não encontrada.")
            return

        total_chars = count_characters_without_timecodes(raw)
        quota = self.app.client.get_user_quota(api_key)
        if quota.valid and quota.character_limit > 0:
            available = max(0, quota.character_limit - quota.character_count)
            if total_chars > available:
                messagebox.showerror(
                    "Cota insuficiente",
                    f"Texto estimado: {total_chars} caracteres.\n"
                    f"Disponível na conta: {available} (limite {quota.character_limit}, usados {quota.character_count}).\n\n"
                    "Reduza o texto ou utilize outra conta.",
                )
                return

        self.cancel_event.clear()
        self.progresso["value"] = 0
        self.progresso["maximum"] = len(texts)
        self.progresso_label.config(text="Progresso: 0%")
        self.mensagem_label.config(text="Iniciando geração...")

        self.worker_thread = threading.Thread(
            target=self._worker_generate_audio,
            name=f"worker-{self.tab_name}",
            daemon=True,
            args=(api_key, voice_id, voz, starts, ends, texts, pasta),
        )
        self.worker_thread.start()

    def _worker_generate_audio(
        self,
        api_key: str,
        voice_id: str,
        voz_nome: str,
        starts_ms: List[int],
        ends_ms: List[int],
        texts: List[str],
        pasta_destino: str,
    ) -> None:
        try:
            audio_final = AudioSegment.silent(duration=0)
            tempo_atual_ms = 0

            for i, texto in enumerate(texts, start=1):
                idx = i - 1
                if self.cancel_event.is_set():
                    self.app.ui_queue.put(UiEvent(self.tab_name, "message", "Geração cancelada."))
                    return

                texto_curto = (texto[:25] + "...") if len(texto) > 25 else texto
                pct = (i / len(texts)) * 100.0
                self.app.ui_queue.put(
                    UiEvent(self.tab_name, "progress", {"i": i, "n": len(texts), "pct": pct, "texto": texto_curto})
                )

                start = starts_ms[idx]
                end = ends_ms[idx]
                window_ms = max(0, end - start)

                mode = self.app.audio_mode.get()
                if mode == self.app.AUDIO_MODE_YOUTUBE:
                    seg_audio = self._generate_segment_single_call_youtube(api_key, voice_id, texto, window_ms)
                else:
                    seg_audio = self._generate_segment_single_call_postfit(api_key, voice_id, texto, window_ms)

                # alinhar START absoluto
                silencio_ms = max(0, start - tempo_atual_ms)
                if silencio_ms:
                    audio_final += AudioSegment.silent(duration=silencio_ms)
                    tempo_atual_ms += silencio_ms

                audio_final += seg_audio
                tempo_atual_ms += len(seg_audio)

                # completar até END com silêncio
                tail_ms = max(0, end - tempo_atual_ms)
                if tail_ms:
                    audio_final += AudioSegment.silent(duration=tail_ms)
                    tempo_atual_ms += tail_ms

                if tempo_atual_ms > end + 5:
                    self.app.ui_queue.put(
                        UiEvent(
                            self.tab_name,
                            "message",
                            "Aviso: uma frase ultrapassou o END definido. Isso pode atrasar as frases seguintes.",
                        )
                    )

            safe_voz = re.sub(r'[\\/*?:"<>|]', "_", voz_nome)
            nome_base = safe_voz
            nome_arquivo = f"{nome_base}.mp3"
            save_path = os.path.join(pasta_destino, nome_arquivo)
            contador = 1
            while os.path.exists(save_path):
                nome_arquivo = f"{nome_base}_{contador}.mp3"
                save_path = os.path.join(pasta_destino, nome_arquivo)
                contador += 1

            audio_final.export(save_path, format="mp3")
            self.app.ui_queue.put(UiEvent(self.tab_name, "done", {"nome": nome_arquivo, "path": save_path}))


        except Exception as e:

            logger.exception("Falha no worker de geração")

            self.app.ui_queue.put(UiEvent(self.tab_name, "error", f"{e}\n\nVeja o log em:\n{LOG_FILE}"))

    # -----------------------------
    # Áudio: FFmpeg atempo / fitting rules (modo PADRÃO)
    # -----------------------------

    @staticmethod
    def _ffmpeg_atempo(audio: AudioSegment, factor: float) -> AudioSegment:
        factor = float(factor)
        filters: List[str] = []
        f = factor
        while f > 2.0:
            filters.append("atempo=2.0")
            f /= 2.0
        while f < 0.5:
            filters.append("atempo=0.5")
            f /= 0.5
        filters.append(f"atempo={f:.6f}")
        afilter = ",".join(filters)

        fin = tempfile.NamedTemporaryFile(suffix=".wav", delete=False)
        fout = tempfile.NamedTemporaryFile(suffix=".wav", delete=False)
        in_path = fin.name
        out_path = fout.name
        fin.close()
        fout.close()

        try:
            audio.export(in_path, format="wav")
            cmd = ["ffmpeg", "-y", "-i", in_path, "-filter:a", afilter, out_path]
            subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            return AudioSegment.from_file(out_path, format="wav")
        finally:
            for p in (in_path, out_path):
                try:
                    os.remove(p)
                except Exception:
                    pass

    def _apply_speed(self, audio: AudioSegment, factor: float) -> AudioSegment:
        if abs(float(factor) - 1.0) < 1e-3:
            return audio
        return self._ffmpeg_atempo(audio, float(factor))

    def _fit_small_audio(self, audio: AudioSegment, window_ms: int) -> Tuple[AudioSegment, float, str]:
        if window_ms <= 0 or len(audio) <= 0:
            return audio, 1.0, "none"

        ratio = len(audio) / float(window_ms)
        if ratio >= 1.0:
            return audio, 1.0, "none"

        factor = max(ratio, 0.90)  # não desacelera abaixo de 90%
        if abs(factor - 1.0) < 1e-3:
            return audio, 1.0, "none"

        adjusted = self._apply_speed(audio, factor)
        return adjusted, factor, "slowed_down"

    def _fit_big_audio_progressive(self, audio_edge_trimmed: AudioSegment, window_ms: int) -> Tuple[AudioSegment, float, str]:
        if window_ms <= 0 or len(audio_edge_trimmed) <= 0:
            return audio_edge_trimmed, 1.0, "none"

        needed = len(audio_edge_trimmed) / float(window_ms)
        factor1 = min(needed, 1.20)
        audio1 = audio_edge_trimmed
        used1 = 1.0
        if factor1 > 1.0 + 1e-3:
            audio1 = self._apply_speed(audio_edge_trimmed, factor1)
            used1 = factor1
        if len(audio1) <= window_ms + 5:
            return audio1, used1, "sped_up_<=1.20"

        audio2_base = self._compress_internal_silences(
            audio_edge_trimmed,
            min_silence_len=160,
            silence_thresh_offset_db=16.0,
            keep_edge_ms=55,
            min_gap_ms=45,
            max_gap_ms=90,
        )
        needed2 = len(audio2_base) / float(window_ms)
        factor2 = min(needed2, 1.20)
        audio2 = audio2_base
        used2 = 1.0
        if factor2 > 1.0 + 1e-3:
            audio2 = self._apply_speed(audio2_base, factor2)
            used2 = factor2
        if len(audio2) <= window_ms + 5:
            return audio2, used2, "sped_up_after_silences_<=1.20"

        needed3 = len(audio2_base) / float(window_ms)
        factor3 = max(1.0, needed3)

        # cap de segurança contra timecode errado. Aumente/diminua se quiser.
        factor3 = min(factor3, 4.0)

        audio3 = self._apply_speed(audio2_base, factor3)

        if len(audio3) > window_ms + 5:
            needed4 = len(audio3) / float(window_ms)
            factor4 = max(1.0, needed4)
            factor4 = min(factor4, 2.0)
            audio3 = self._apply_speed(audio3, factor4)
            factor3 *= factor4

        return audio3, factor3, "sped_up_over_1.20"

    # -----------------------------
    # Geradores por modo
    # -----------------------------

    def _generate_segment_single_call_postfit(self, api_key: str, voice_id: str, text: str, window_ms: int) -> AudioSegment:
        """
        Modo PADRÃO (fit): trim bordas sempre + speed adaptativo e compressão conforme regra.
        """
        if self.cancel_event.is_set():
            raise RuntimeError("Cancelado pelo usuário.")

        with self.app.tts_request_lock:
            if self.cancel_event.is_set():
                raise RuntimeError("Cancelado pelo usuário.")
            result = self._call_tts_once(api_key, voice_id, text, speed=1.0)

        raw_audio = AudioSegment.from_file(io.BytesIO(result.mp3_bytes), format="mp3")

        # sempre remove silêncio inicial/final
        audio_edge_trimmed = self._trim_with_alignment(raw_audio, result)

        if window_ms > 0 and len(audio_edge_trimmed) > window_ms + 5:
            audio_fit, factor, mode = self._fit_big_audio_progressive(audio_edge_trimmed, window_ms)
            if mode == "sped_up_<=1.20":
                self.app.ui_queue.put(
                    UiEvent(self.tab_name, "message", f"Padrão: áudio grande acelerado {factor*100:.0f}% (≤120%).")
                )
            elif mode == "sped_up_after_silences_<=1.20":
                self.app.ui_queue.put(
                    UiEvent(self.tab_name, "message", f"Padrão: cortei silêncios e acelerei {factor*100:.0f}% (≤120%).")
                )
            else:
                self.app.ui_queue.put(UiEvent(self.tab_name, "message", f"Padrão: precisei >120%. Acelerei {factor*100:.0f}% para caber."))
            return audio_fit

        audio_fit, factor, mode = self._fit_small_audio(audio_edge_trimmed, window_ms)
        if mode == "slowed_down":
            self.app.ui_queue.put(UiEvent(self.tab_name, "message", f"Padrão: áudio pequeno desacelerado {factor*100:.0f}% (≥90%)."))
        return audio_fit

    def _generate_segment_single_call_youtube(self, api_key: str, voice_id: str, text: str, window_ms: int) -> AudioSegment:
        """
        Modo YOUTUBE:
        - Se couber: retorna raw_audio (igual ElevenLabs).
        - Se não couber: corta silêncios (bordas + internos) sem mexer em speed.
        """
        if self.cancel_event.is_set():
            raise RuntimeError("Cancelado pelo usuário.")

        with self.app.tts_request_lock:
            if self.cancel_event.is_set():
                raise RuntimeError("Cancelado pelo usuário.")
            result = self._call_tts_once(api_key, voice_id, text, speed=1.0)

        raw_audio = AudioSegment.from_file(io.BytesIO(result.mp3_bytes), format="mp3")

        if window_ms > 0 and len(raw_audio) <= window_ms + 5:
            return raw_audio

        audio_t = self._trim_with_alignment(raw_audio, result)
        audio_c = self._compress_internal_silences(
            audio_t,
            min_silence_len=220,
            silence_thresh_offset_db=14.5,
            keep_edge_ms=120,
            min_gap_ms=60,
            max_gap_ms=110,
        )

        if window_ms > 0 and len(audio_c) <= window_ms + 5:
            self.app.ui_queue.put(UiEvent(self.tab_name, "message", "YouTube: não cabia; cortei silêncios para encaixar (sem speed)."))
            return audio_c

        self.app.ui_queue.put(UiEvent(self.tab_name, "message", "YouTube: mesmo cortando silêncios não coube. Mantive overflow (sem speed)."))
        return audio_c

    # -----------------------------
    # Trim / Compress (helpers)
    # -----------------------------

    @staticmethod
    def _safe_dbfs(seg: AudioSegment, fallback: float = -60.0) -> float:
        try:
            v = float(seg.dBFS)
            if v == float("-inf") or v != v:
                return fallback
            return v
        except Exception:
            return fallback

    def _trim_with_alignment(self, audio: AudioSegment, result: TtsWithTimingResult) -> AudioSegment:
        n = len(audio)
        if n <= 0:
            return audio

        align_start = 0
        align_end = n

        if result.speech_start_seconds is not None:
            align_start = int(result.speech_start_seconds * 1000) - self.app.LEAD_TRIM_PADDING_MS
        if result.speech_end_seconds is not None:
            align_end = int(result.speech_end_seconds * 1000) + self.app.END_TRIM_PADDING_MS

        align_start = max(0, min(align_start, n))
        align_end = max(0, min(align_end, n))
        if align_end <= align_start:
            return audio

        start_ms = align_start
        end_ms = align_end

        try:
            base_dbfs = self._safe_dbfs(audio)
            base_thresh = base_dbfs - float(self.app.NONSILENT_THRESH_OFFSET_DB)
            silence_thresh = min(base_thresh, -42.0)

            ranges = detect_nonsilent(
                audio,
                min_silence_len=int(self.app.NONSILENT_MIN_SILENCE_LEN),
                silence_thresh=silence_thresh,
                seek_step=1,
            )

            if ranges:
                energy_start = max(0, ranges[0][0] - int(self.app.NONSILENT_GUARD_MS))
                energy_end = min(n, ranges[-1][1] + int(self.app.NONSILENT_GUARD_MS))
                start_ms = min(start_ms, energy_start)
                end_ms = max(end_ms, energy_end)

            tail_probe_ms = 450
            tail_start = max(0, n - tail_probe_ms)
            tail = audio[tail_start:n]
            tail_dbfs = self._safe_dbfs(tail)
            tail_thresh = min(tail_dbfs - (float(self.app.NONSILENT_THRESH_OFFSET_DB) + 4.0), -45.0)
            tail_ranges = detect_nonsilent(
                tail,
                min_silence_len=max(35, int(self.app.NONSILENT_MIN_SILENCE_LEN * 0.6)),
                silence_thresh=tail_thresh,
                seek_step=1,
            )
            if tail_ranges:
                last_end = tail_start + tail_ranges[-1][1]
                end_ms = max(end_ms, min(n, last_end + int(self.app.NONSILENT_GUARD_MS)))
        except Exception:
            pass

        if start_ms > int(self.app.MAX_HEAD_TRIM_MS):
            start_ms = int(self.app.MAX_HEAD_TRIM_MS)

        tail_trim = n - end_ms
        if tail_trim > int(self.app.MAX_TAIL_TRIM_MS):
            end_ms = n - int(self.app.MAX_TAIL_TRIM_MS)

        start_ms = max(0, min(start_ms, n))
        end_ms = max(0, min(end_ms, n))
        if end_ms <= start_ms:
            return audio

        out = audio[start_ms:end_ms]
        try:
            out = out.fade_in(5).fade_out(10)
        except Exception:
            pass
        return out

    def _compress_internal_silences(
        self,
        audio: AudioSegment,
        *,
        min_silence_len: int = 160,
        silence_thresh_offset_db: float = 16.0,
        keep_edge_ms: int = 30,
        min_gap_ms: int = 45,
        max_gap_ms: int = 90,
    ) -> AudioSegment:
        if len(audio) <= 0:
            return audio

        base_dbfs = self._safe_dbfs(audio)
        base_thresh = base_dbfs - silence_thresh_offset_db
        silence_thresh = min(base_thresh, -42.0)

        ranges = detect_nonsilent(audio, min_silence_len=min_silence_len, silence_thresh=silence_thresh, seek_step=1)
        if not ranges:
            return audio

        n = len(audio)

        def clamp(v: int) -> int:
            return max(0, min(v, n))

        protected: List[Tuple[int, int]] = []
        for start, end in ranges:
            s = clamp(start - keep_edge_ms)
            e = clamp(end + keep_edge_ms)
            if protected and s <= protected[-1][1]:
                protected[-1] = (protected[-1][0], max(protected[-1][1], e))
            else:
                protected.append((s, e))

        out = AudioSegment.empty()
        out += audio[protected[0][0] : protected[0][1]]
        prev_end = protected[0][1]

        for start, end in protected[1:]:
            gap = max(0, start - prev_end)
            if gap > 0:
                gap_kept = max(min_gap_ms, min(max_gap_ms, gap))
                out += AudioSegment.silent(duration=gap_kept)
            out += audio[start:end]
            prev_end = end

        if prev_end < n:
            tail = audio[prev_end:n]
            if len(tail) > 0:
                tail_dbfs = self._safe_dbfs(tail)
                tail_thresh = min(tail_dbfs - (silence_thresh_offset_db + 4.0), -45.0)
                tail_ranges = detect_nonsilent(
                    tail,
                    min_silence_len=max(40, int(min_silence_len * 0.6)),
                    silence_thresh=tail_thresh,
                    seek_step=1,
                )
                if tail_ranges:
                    last_end = tail_ranges[-1][1]
                    keep_until = min(len(tail), last_end + keep_edge_ms)
                    out += tail[:keep_until]

        return out

    # -----------------------------
    # TTS call (sem retries)
    # -----------------------------

    def _call_tts_once(self, api_key: str, voice_id: str, text: str, speed: float) -> TtsWithTimingResult:
        if self.cancel_event.is_set():
            raise RuntimeError("Cancelado pelo usuário.")

        return self.app.client.tts_with_timestamps(
            api_key=api_key,
            voice_id=voice_id,
            text=text,
            stability=self.app.STABILITY_PADRAO / 100,
            similarity_boost=self.app.SIMILARITY_PADRAO / 100,
            style_exaggeration=self.app.STYLE_PADRAO / 100,
            speed=speed,
            model_id="eleven_multilingual_v2",
        )


# -----------------------------
# Aba Manager
# -----------------------------


class AbaGerenciador:
    def __init__(self, notebook: ttk.Notebook, app: "App"):
        self.notebook = notebook
        self.app = app
        self.abas_ativas = set()

        self.menu_contexto = ttkb.Menu(self.notebook, tearoff=0)
        self.menu_contexto.add_command(label="Fechar Aba", command=self.fechar_aba_selecionada)

        self.notebook.bind("<Button-3>", self.exibir_menu_contexto)
        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_changed)

        self.criar_aba_inicial()
        self.criar_aba_adicionar()

    def criar_aba_inicial(self):
        self._criar_aba_numero(1)

    def criar_aba_adicionar(self):
        aba_adicionar = ttk.Frame(self.notebook)
        self.notebook.add(aba_adicionar, text="+")

    def _criar_aba_numero(self, numero: int):
        aba_nome = f"T{numero}"
        aba = ttk.Frame(self.notebook)
        self.notebook.add(aba, text=aba_nome)
        self.abas_ativas.add(numero)

        self.app.tabs[aba_nome] = TabUI(aba, aba_nome, self.app)
        self.app.apply_voice_preset_for_tab(aba_nome)

    def adicionar_aba(self):
        numero_aba = 1
        while numero_aba in self.abas_ativas:
            numero_aba += 1
        self._criar_aba_numero(numero_aba)

    def on_tab_changed(self, _event):
        current = self.notebook.index("current")
        if current == len(self.notebook.tabs()) - 1:
            self.notebook.forget(current)
            self.adicionar_aba()
            self.notebook.select(self.notebook.index("end") - 1)
            self.criar_aba_adicionar()

    def exibir_menu_contexto(self, event):
        try:
            aba_indice = self.notebook.index(f"@{event.x},{event.y}")
            self.notebook.select(aba_indice)
            self.menu_contexto.post(event.x_root, event.y_root)
        except Exception:
            pass

    def fechar_aba_selecionada(self):
        aba_indice = self.notebook.index("current")
        aba_nome = self.notebook.tab(aba_indice, "text")

        if aba_nome in ("T1", "+"):
            return

        tab = self.app.tabs.get(aba_nome)
        if tab and tab.worker_thread and tab.worker_thread.is_alive():
            resp = messagebox.askyesno(
                "Aviso",
                f"Uma geração está em andamento na aba {aba_nome}.\nDeseja cancelar e fechar a aba?",
            )
            if not resp:
                return
            tab.cancel_generation()

        try:
            numero_aba = int(aba_nome[1:])
            self.abas_ativas.discard(numero_aba)
        except Exception:
            pass

        self.app.tabs.pop(aba_nome, None)
        self.notebook.forget(aba_indice)

        if aba_indice > 0 and len(self.notebook.tabs()) > 0:
            self.notebook.select(aba_indice - 1)
        elif len(self.notebook.tabs()) > 0:
            self.notebook.select(0)


# -----------------------------
# Main App
# -----------------------------


class App:
    STABILITY_PADRAO = 50
    SIMILARITY_PADRAO = 70
    STYLE_PADRAO = 0

    LEAD_TRIM_PADDING_MS = 90
    END_TRIM_PADDING_MS = 260

    NONSILENT_MIN_SILENCE_LEN = 50
    NONSILENT_THRESH_OFFSET_DB = 18.0
    NONSILENT_GUARD_MS = 140

    MAX_HEAD_TRIM_MS = 250
    MAX_TAIL_TRIM_MS = 350

    AUDIO_MODE_PADRAO = "padrao"
    AUDIO_MODE_YOUTUBE = "youtube"

    VOICE_PRESETS_BY_TAB = {
        "T1": "ESP - Audrey",
        "T2": "ESP - Audrey",
        "T3": "FRA - Clara Dupont",
        "T4": "ALE - Emilia German",
        "T5": "TUR - Sultan",
        "T6": "ING - Hope",
        "T7": "Keren - Young Brazilian Female",
    }

    def __init__(self):
        self.config_store = ConfigStore(CONFIG_FILE)
        self.sound_store = NotificationSoundStore(NOTIFICATION_SOUND_FILE)
        self.key_store = ApiKeyStore(API_KEYS_FILE)
        self.client = ElevenLabsClient()

        # Lock global: apenas 1 chamada TTS por vez (entre todas as abas)
        self.tts_request_lock = threading.Lock()

        self.all_voices: List[Dict[str, Any]] = []
        self.audios_gerados: List[AudioRecord] = []

        self.ui_queue: "Queue[UiEvent]" = Queue()
        self.tabs: Dict[str, TabUI] = {}

        self.mixer_ok = False
        if PYGAME_AVAILABLE:
            try:
                mixer.init()
                self.mixer_ok = True
            except Exception:
                logger.exception("Falha ao inicializar pygame.mixer")
                self.mixer_ok = False

        self.root = ttkb.Window(themename="darkly")
        self.root.title("Gerador")

        # --- Ícone do app ---
        try:
            icon_path = os.path.join(os.path.dirname(__file__), "assets", "motapp.ico")
            if os.path.exists(icon_path):
                self.root.iconbitmap(icon_path)  # Windows (.ico)
        except Exception:
            logger.exception("Falha ao aplicar ícone .ico")
        try:
            base_dir = os.path.dirname(__file__)
            ico_path = os.path.join(base_dir, "assets", "motapp.ico")
            png_path = os.path.join(base_dir, "assets", "motapp.png")

            if os.path.exists(ico_path):
                self.root.iconbitmap(ico_path)
            elif os.path.exists(png_path):
                img = ttkb.PhotoImage(file=png_path)
                self.root.iconphoto(True, img)
                self._app_icon_img = img  # evita o GC destruir a imagem
        except Exception:
            logger.exception("Falha ao aplicar ícone")

        self.root.geometry("920x540")
        self.root.eval("tk::PlaceWindow . center")

        self.api_key_selecionada = StringVar(self.root, value="")
        self.audio_mode = StringVar(self.root, value=self.AUDIO_MODE_PADRAO)

        self.audio_mode_ui = StringVar(self.root, value="Padrão")

        self.label_caracteres = None
        self.treeview_audios = None

        self._build_ui()
        self._load_initial_state()

        self.root.after(100, self._poll_ui_events)
        self.root.protocol("WM_DELETE_WINDOW", self.close)

    # -----------------------------
    # Presets
    # -----------------------------

    def apply_voice_preset_for_tab(self, tab_name: str) -> None:
        preset = self.VOICE_PRESETS_BY_TAB.get(tab_name)
        if not preset:
            return
        tab = self.tabs.get(tab_name)
        if not tab:
            return
        if not self.all_voices:
            return

        if self.get_voice_id_by_name(preset):
            tab.filtro_voz.set(preset)
            tab.combobox_vozes.set(preset)
            tab._set_placeholder_state(False)
        else:
            try:
                tab.mensagem_label.config(text=f"Preset '{preset}' não encontrado na conta atual.")
            except Exception:
                pass

    def apply_voice_presets_all_tabs(self) -> None:
        for tab_name in list(self.tabs.keys()):
            self.apply_voice_preset_for_tab(tab_name)

    # -----------------------------
    # Exportar textos (menu)
    # -----------------------------

    def export_all_tabs_text(self) -> None:
        """
        Exporta o conteúdo de texto de TODAS as abas (T1, T2, ...) para arquivos .txt.
        Salva 1 TXT por aba automaticamente.
        """
        pasta = filedialog.askdirectory(title="Selecione a pasta para salvar os TXTs (todas as abas)")
        if not pasta:
            return

        exported = 0
        skipped = 0

        for tab_name, tab in self.tabs.items():
            try:
                raw = tab.entrada_texto.get("1.0", "end-1c").strip()
                if not raw:
                    skipped += 1
                    continue

                voz = tab.combobox_vozes.get().strip()
                if not voz or voz == "Selecione a voz":
                    voz = "SEM_VOZ"

                safe_voz = re.sub(r'[\\/*?:"<>|]', "_", voz)
                nome_arquivo = f"{tab_name}_{safe_voz}.txt"
                path = os.path.join(pasta, nome_arquivo)

                contador = 1
                while os.path.exists(path):
                    nome_arquivo = f"{tab_name}_{safe_voz}_{contador}.txt"
                    path = os.path.join(pasta, nome_arquivo)
                    contador += 1

                with open(path, "w", encoding="utf-8") as f:
                    f.write(raw)

                exported += 1
            except Exception:
                logger.exception("Falha ao exportar texto da aba %s", tab_name)
                skipped += 1

        messagebox.showinfo(
            "Exportação concluída",
            f"Arquivos exportados: {exported}\nAbas sem conteúdo / com erro: {skipped}\n\nPasta:\n{pasta}",
        )

    # -----------------------------
    # UI
    # -----------------------------

    def _build_ui(self) -> None:
        menu_bar = ttkb.Menu(self.root)
        opcoes_menu = ttkb.Menu(menu_bar, tearoff=0)

        tema_menu = ttkb.Menu(opcoes_menu, tearoff=0)
        for t in ("superhero", "darkly", "flatly"):
            tema_menu.add_command(label=t.capitalize(), command=lambda x=t: self.alterar_tema(x))
        opcoes_menu.add_cascade(label="Temas", menu=tema_menu)

        self.api_menu = ttkb.Menu(opcoes_menu, tearoff=0)
        opcoes_menu.add_cascade(label="Contas API", menu=self.api_menu)


        # ✅ exportar texto de todas as abas
        opcoes_menu.add_command(label="Exportar textos de todas as abas", command=self.export_all_tabs_text)

        opcoes_menu.add_command(label="Reaplicar Presets de Voz", command=self.apply_voice_presets_all_tabs)
        opcoes_menu.add_command(label="Áudios Gerados", command=self.abrir_janela_audios)
        opcoes_menu.add_command(label="Som de Notificação", command=self.selecionar_som_notificacao)

        ajuda_menu = ttkb.Menu(opcoes_menu, tearoff=0)
        ajuda_menu.add_command(label="Exibir Ajuda", command=self.exibir_ajuda)
        opcoes_menu.add_cascade(label="Ajuda", menu=ajuda_menu)

        # -----------------------------
        # Topbar (☰ + Toggle Modo)
        # -----------------------------
        topbar = ttkb.Frame(self.root, padding=(10, 6))
        topbar.pack(side="top", fill="x")

        # Botão ☰ (abre o mesmo menu opcoes_menu)
        btn_menu = ttkb.Button(
            topbar,
            text="☰",
            width=3,
            bootstyle="secondary",
            command=lambda: opcoes_menu.post(
                btn_menu.winfo_rootx(),
                btn_menu.winfo_rooty() + btn_menu.winfo_height(),
            ),
        )
        btn_menu.pack(side="left")

        self.modo_toggle = ttkb.Checkbutton(
            topbar,
            text="Modo: Padrão",  # texto inicial (vai ser atualizado)
            variable=self.audio_mode,
            onvalue=self.AUDIO_MODE_YOUTUBE,
            offvalue=self.AUDIO_MODE_PADRAO,
            bootstyle="success-round-toggle",
            command=self._save_config_quick(),  # ✅ chama quando clicar
        )
        self.modo_toggle.pack(side="left", padx=(10, 0))

        # ✅ mantém o texto do toggle sempre sincronizado com o valor
        self.audio_mode.trace_add("write", lambda *_: self._sync_toggle_text())
        self._sync_toggle_text()

        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True)

        self.gerenciador_abas = AbaGerenciador(self.notebook, self)

        footer = ttkb.Frame(self.root, padding=(10, 6))
        footer.pack(side="bottom", fill="x")

        self.label_caracteres = ttkb.Label(footer, text="Carregando dados...", bootstyle="secondary")
        self.label_caracteres.pack(side="left", anchor="w")


    def _load_initial_state(self) -> None:
        config = self.config_store.load()
        self.root.style.theme_use(config.get("tema", "darkly"))

        mode = str(config.get("audio_mode", self.AUDIO_MODE_PADRAO)).strip().lower()
        if mode in (self.AUDIO_MODE_PADRAO, self.AUDIO_MODE_YOUTUBE):
            self.audio_mode.set(mode)
        else:
            self.audio_mode.set(self.AUDIO_MODE_PADRAO)

        keys = self.key_store.load()
        ultima = config.get("ultima_conta", "")

        if ultima and ultima in keys:
            self.api_key_selecionada.set(ultima)
        elif keys:
            self.api_key_selecionada.set(list(keys.keys())[0])
        else:
            self.api_key_selecionada.set("")

        self.atualizar_menu_contas()
        self.refresh_quota_label()
        if self.get_selected_api_key():
            self.load_voices()

    # -----------------------------
    # Dados (API / vozes / quota)
    # -----------------------------

    def get_selected_api_key(self) -> Optional[str]:
        conta = self.api_key_selecionada.get().strip()
        if not conta:
            return None
        keys = self.key_store.load()
        return keys.get(conta)

    def get_voice_id_by_name(self, nome_voz: str) -> Optional[str]:
        for v in self.all_voices:
            if v.get("name", "").strip().lower() == nome_voz.strip().lower():
                return v.get("voice_id")
        return None

    def alterar_tema(self, nome_tema: str) -> None:
        try:
            self.root.style.theme_use(nome_tema)
        except Exception:
            logger.exception("Falha ao trocar tema")
            messagebox.showerror("Erro", "Não foi possível alterar o tema.")

    def atualizar_menu_contas(self) -> None:
        self.api_menu.delete(0, "end")
        keys = self.key_store.load()

        for conta in keys.keys():
            self.api_menu.add_radiobutton(
                label=conta,
                variable=self.api_key_selecionada,
                command=lambda c=conta: self.alterar_chave_api(c),
            )

        self.api_menu.add_separator()
        self.api_menu.add_command(label="Adicionar Nova Chave API", command=self.adicionar_chave_api)
        self.api_menu.add_command(label="Excluir Chave API", command=self.excluir_chave_api)

        self.api_key_selecionada.set(self.api_key_selecionada.get())

    def alterar_chave_api(self, conta: str) -> None:
        self.api_key_selecionada.set(conta)
        self.load_voices()
        self.refresh_quota_label()

    def adicionar_chave_api(self) -> None:
        keys = self.key_store.load()
        nome = simpledialog.askstring("Nome da Conta", "Digite o nome da conta:", parent=self.root)
        if not nome:
            return
        nome = nome.strip()
        if nome in keys:
            messagebox.showerror("Erro", f"Já existe uma conta com o nome '{nome}'.")
            return

        nova = simpledialog.askstring("Nova Chave API", "Digite a nova chave API:", parent=self.root)
        if not nova:
            return
        nova = nova.strip()

        messagebox.showinfo("Validação", "Validando a chave API, por favor aguarde...")
        quota = self.client.get_user_quota(nova)

        if quota.valid:
            keys[nome] = nova
            self.key_store.save(keys)
            self.api_key_selecionada.set(nome)
            self.atualizar_menu_contas()
            self.load_voices()
            self.refresh_quota_label()
            messagebox.showinfo("Sucesso", "Chave API válida adicionada com sucesso!")
        else:
            messagebox.showerror("Erro de Validação", quota.error or "Não foi possível validar a chave.")

    def excluir_chave_api(self) -> None:
        keys = self.key_store.load()
        if not keys:
            messagebox.showinfo("Informação", "Nenhuma chave de API cadastrada.")
            return

        contas = list(keys.keys())
        conta = simpledialog.askstring(
            "Excluir Chave API",
            "Digite o nome da conta que deseja excluir:\n" + "\n".join(contas),
            parent=self.root,
        )
        if not conta:
            return
        conta = conta.strip()

        if conta not in keys:
            messagebox.showerror("Erro", "Conta não encontrada.")
            return

        del keys[conta]
        self.key_store.save(keys)
        self.atualizar_menu_contas()

        if not keys:
            self.api_key_selecionada.set("")
            self.all_voices = []
            self.refresh_all_tabs_voice_list()
            self.label_caracteres.config(text="Sem chave API selecionada.")
        else:
            self.api_key_selecionada.set(list(keys.keys())[0])
            self.load_voices()
            self.refresh_quota_label()

        messagebox.showinfo("Sucesso", f"A conta '{conta}' foi excluída com sucesso!")

    def selecionar_som_notificacao(self) -> None:
        tipos = (("Arquivos de áudio", "*.mp3 *.wav"), ("Todos os arquivos", "*.*"))
        arquivo = filedialog.askopenfilename(title="Selecione o som de notificação", filetypes=tipos)
        if arquivo:
            self.sound_store.save(arquivo)
            messagebox.showinfo("Sucesso", "Som de notificação configurado com sucesso!")

    def tocar_som_notificacao(self) -> None:
        if not (self.mixer_ok and mixer):
            return
        config = self.sound_store.load()
        caminho = config.get("caminho_som")
        if caminho and os.path.exists(caminho):
            try:
                mixer.music.load(caminho)
                mixer.music.play()
            except Exception:
                logger.exception("Falha ao tocar som de notificação")

    def load_voices(self) -> None:
        api_key = self.get_selected_api_key()
        if not api_key:
            messagebox.showerror("Erro", "Nenhuma chave de API selecionada ou inválida.")
            return

        try:
            self.all_voices = self.client.list_voices(api_key)
            self.refresh_all_tabs_voice_list()
            self.apply_voice_presets_all_tabs()
        except requests.exceptions.HTTPError as e:
            logger.exception("Erro HTTP ao obter vozes")
            messagebox.showerror("Erro de API", f"Erro HTTP ao obter vozes: {e}")
        except requests.exceptions.RequestException as e:
            logger.exception("Erro de rede ao obter vozes")
            messagebox.showerror("Erro de Conexão", f"Não foi possível obter vozes. Verifique sua conexão.\n{e}")
        except Exception as e:
            logger.exception("Erro inesperado ao obter vozes")
            messagebox.showerror("Erro", f"Ocorreu um erro inesperado ao obter vozes: {e}")

    def refresh_all_tabs_voice_list(self) -> None:
        for tab in self.tabs.values():
            tab.refresh_voice_list()

    def refresh_quota_label(self) -> None:
        api_key = self.get_selected_api_key()
        conta = self.api_key_selecionada.get().strip()
        if not api_key:
            self.label_caracteres.config(text="Sem chave API selecionada.")
            return

        quota = self.client.get_user_quota(api_key)
        if quota.valid and quota.character_limit > 0:
            pct = (quota.character_count / quota.character_limit) * 100.0
            self.label_caracteres.config(text=f"Cota {conta}: {quota.character_count}/{quota.character_limit} ({pct:.2f}%)")
        elif quota.valid:
            self.label_caracteres.config(text=f"Cota {conta}: limite de caracteres não definido.")
        else:
            self.label_caracteres.config(text=f"Cota {conta}: chave inválida ou erro de consulta.")

    # -----------------------------
    # Janelas auxiliares
    # -----------------------------

    def abrir_janela_audios(self) -> None:
        win = ttkb.Toplevel(self.root)
        win.title("Áudios Gerados")
        win.geometry("700x400")

        frame = ttkb.Frame(win, padding=10)
        frame.pack(fill="both", expand=True)

        colunas = ("Nome", "Caminho", "Status")
        tree = ttk.Treeview(frame, columns=colunas, show="headings")
        tree.heading("Nome", text="Nome do Arquivo")
        tree.heading("Caminho", text="Caminho")
        tree.heading("Status", text="Status")
        tree.pack(fill="both", expand=True, pady=10)

        self.treeview_audios = tree

        for rec in self.audios_gerados:
            tree.insert("", "end", values=(rec.nome, rec.caminho, rec.status))

        def abrir_pasta_com_selecao(_event):
            item = tree.selection()
            if not item:
                return
            caminho = tree.item(item, "values")[1]
            if os.path.exists(caminho):
                subprocess.run(["explorer", "/select,", os.path.normpath(caminho)], check=False)
            else:
                messagebox.showerror("Erro", f"O arquivo {caminho} não foi encontrado.")

        tree.bind("<Double-1>", abrir_pasta_com_selecao)

        def on_close():
            if self.treeview_audios is tree:
                self.treeview_audios = None
            win.destroy()

        win.protocol("WM_DELETE_WINDOW", on_close)

    def exibir_ajuda(self) -> None:
        win = ttkb.Toplevel(self.root)
        win.title("Ajuda")
        win.geometry("760x700")

        frame = ttkb.Frame(win, padding=10)
        frame.pack(fill="both", expand=True)

        texto = ttkb.Text(frame, wrap="word", height=30)
        texto.pack(fill="both", expand=True)
        texto.tag_configure("normal", font=("TkDefaultFont", 10))

        texto_principal = (
            "\n"
            "Modos:\n"
            "  - Padrão: trim bordas sempre + fit por speed/pausas.\n"
            "  - YouTube: se couber, NÃO mexe (igual ElevenLabs). Só corta silêncios se não couber.\n\n"
            "Menu ☰:\n"
            "  - Exportar textos de todas as abas (1 TXT por aba)\n"
            "  - Reaplicar Presets de Voz\n\n"
        )
        texto.insert("1.0", texto_principal, "normal")
        texto.config(state="disabled")

    # -----------------------------
    # Loop de eventos UI
    # -----------------------------

    def _poll_ui_events(self) -> None:
        try:
            while True:
                ev = self.ui_queue.get_nowait()
                self._handle_ui_event(ev)
        except Empty:
            pass
        finally:
            self.root.after(100, self._poll_ui_events)

    def _handle_ui_event(self, ev: UiEvent) -> None:
        tab = self.tabs.get(ev.tab_name)
        if not tab:
            return

        if ev.kind == "progress":
            data = ev.payload or {}
            i = int(data.get("i", 0))
            n = int(data.get("n", 1))
            pct = float(data.get("pct", 0.0))
            texto_curto = str(data.get("texto", ""))

            tab.progresso["maximum"] = n
            tab.progresso["value"] = i
            tab.progresso_label.config(text=f'Progresso: {i}/{n} - "{texto_curto}" ({pct:.1f}%)')

        elif ev.kind == "message":
            tab.mensagem_label.config(text=str(ev.payload or ""))

        elif ev.kind == "error":
            tab.mensagem_label.config(text="Falha na geração.")
            messagebox.showerror("Erro", f"Falha ao gerar áudio:\n{ev.payload}")

        elif ev.kind == "done":
            nome = ev.payload.get("nome")
            path = ev.payload.get("path")
            tab.mensagem_label.config(text=f"Concluído: {nome}")

            rec = AudioRecord(nome=str(nome), caminho=str(path), status="OK")
            self.audios_gerados.append(rec)
            if self.treeview_audios is not None:
                try:
                    self.treeview_audios.insert("", "end", values=(rec.nome, rec.caminho, rec.status))
                except Exception:
                    pass

            self.tocar_som_notificacao()
            self.refresh_quota_label()

    # -----------------------------
    # Encerramento
    # -----------------------------

    def close(self) -> None:
        try:
            self.config_store.save(
                {
                    "tema": self.root.style.theme_use(),
                    "ultima_conta": self.api_key_selecionada.get().strip(),
                    "audio_mode": self.audio_mode.get().strip().lower(),
                }
            )
        except Exception:
            logger.exception("Falha ao salvar config")
        self.root.destroy()

    def run(self) -> None:
        self.root.mainloop()

    def _on_audio_mode_toggled(self) -> None:
        # Aqui você pode mostrar feedback visual/log se quiser
        mode = self.audio_mode.get()
        logger.info("Modo de áudio alterado para: %s", mode)

    def _sync_toggle_text(self) -> None:
        if self.audio_mode.get() == self.AUDIO_MODE_YOUTUBE:
            self.modo_toggle.config(text="Modo: YouTube")
        else:
            self.modo_toggle.config(text="Modo: Curtos")

    def _save_config_quick(self) -> None:
        try:
            self.config_store.save(
                {
                    "tema": self.root.style.theme_use(),
                    "ultima_conta": self.api_key_selecionada.get().strip(),
                    "audio_mode": self.audio_mode.get().strip().lower(),
                }
            )
        except Exception:
            logger.exception("Falha ao salvar config (quick)")


if __name__ == "__main__":
    App().run()