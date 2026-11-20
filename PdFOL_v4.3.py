"""
PdFOL v2.4  (visor de PDF con pestanas + organizar, aplanar, foliar y comprimir) · by Meneses999
========
VISOR    : cada PDF se abre en su pestana, con miniaturas a la izquierda y
           desplazamiento continuo. Las paginas se dibujan en un proceso aparte
           (la ventana nunca se congela) y solo las que se ven.
Herramienta para PDFs grandes de planos:

1. APLANAR  : convierte en imagen de alta resolucion SOLO las paginas pesadas
              (planos con muchos vectores) para que carguen rapido. Las partes
              en blanco y negro se guardan en escala de grises (identicas, pesan
              ~3 veces menos). Conserva marcadores, enlaces y el texto de los
              planos como capa invisible (Ctrl+F). Usa varios nucleos.
2. FOLIAR   : agrega el numero de folio como texto nitido: fuente, tamano,
              negrita, color, posicion, margen, texto antes (Pag., Folio o
              propio), formato "0001" o "0001 / 2000", digitos, numero inicial
              y rango de paginas.
0. ORGANIZAR: ver las paginas en miniatura, ordenarlas arrastrando, mover, copiar,
              cortar, pegar, girar y eliminar paginas, unir varios PDF y ver
              cada pagina en grande. Guarda un PDF nuevo (el original no se toca).
3. COMPRIMIR: reduce el tamano SIN bajar la resolucion:
              Sin perdida (identico) / Equilibrada (JPEG 85) / Alta (JPEG 75).

Orden de proceso: aplanar -> foliar -> comprimir. El original nunca se modifica.

- Interfaz grafica: doble clic (o ejecutar sin argumentos).
- Consola: PdFOL.exe doc.pdf --aplanar --foliar --comprimir equilibrada ...
"""

import copy
import csv
import hashlib
import io
import math
import multiprocessing as mp
import os
import queue
import shutil
import statistics
import sys
import threading
import time
import types
import zlib

_T0 = time.time()


def _tiempo(que):
    """PDFOL_TIEMPOS=1: anota cuanto tarda cada parte del arranque."""
    if os.environ.get("PDFOL_TIEMPOS"):
        print(f"TIEMPO {time.time() - _T0:6.2f} s  {que}", flush=True)


if sys.stdout is None:
    sys.stdout = open(os.devnull, "w")
if sys.stderr is None:
    sys.stderr = open(os.devnull, "w")


# ---- husky (PdFOL_icono_husky.svg) en PNG 256 px
ICONO_PNG_B64 = (
    "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"
    "TkSuQmCC"
)

NOMBRE = "PdFOL"
VERSION = "v4.3"
VERSION_INTERNA = "4.3"
AUTOR = "Meneses999"

# Historial de cambios (se ve en «Acerca de» y en «Novedades», sin entrar a GitHub)
CAMBIOS = [
    ("v4.3", [
        "Cambiar texto como Acrobat/Nitro: se sacan las letras originales del PDF y el fondo queda como estaba "
        "(colores, celdas, sombreados). Antes se tapaba con blanco y se notaba la edición.",
        "Mientras escribís, el recuadro toma el color del fondo y debajo se ve la hoja real sin las letras viejas.",
    ]),
    ("v4.2", [
        "Con dos monitores, el menú del clic derecho aparece en el monitor donde está el programa (antes saltaba a "
        "la pantalla principal). También «ver página» de Organizar y la ventana al abrir (vuelve a su monitor).",
        "Menú del clic derecho moderno, como Windows 11: íconos de línea por acción, realce en pastilla, "
        "encabezado con la página, sombra de Windows y aparición suave.",
    ]),
    ("v4.1.1", [
        "Texto en la hoja: botón «✓ Listo»; el clic afuera ya no se pierde ni crea otro recuadro; los textos "
        "puestos se eligen con un clic (aunque el panel Texto esté cerrado).",
        "Los recuadros cambian de tamaño como una autoforma de Word: 8 tiradores (ancho, alto o ambos) y el "
        "puntero muestra qué hace cada uno.",
        "Al borrar todo el texto de un recuadro, el recuadro se quita sin dejar marca.",
    ]),
    ("v4.1", [
        "Editar texto directo en la hoja: al agregar o cambiar un texto se escribe ahí mismo, en un recuadro con "
        "tiradores como en Word. El borde lo mueve y los costados cambian el ancho. Clic adentro para corregirlo.",
        "Los párrafos cambiados del PDF ahora también se pueden mover.",
        "Escaneos: el texto de la página en la que estás se reconoce solo (OCR, sin internet). Después se "
        "selecciona, se copia y se cambia como cualquier texto. Clic derecho: «Copiar todo el texto reconocido».",
        "Menú del clic derecho renovado: con sombra, íconos en color y atajos como teclas.",
    ]),
    ("v4.0.1", [
        "Inicio: al elegir un PDF reciente (o abrir uno) se ve enseguida; ya no hace falta tocar su pestaña.",
        "Las barras de desplazamiento se vuelven a poder tomar y arrastrar (visor, miniaturas y Organizar).",
    ]),
    ("v4.0", [
        "Más rápido y liviano: al abrir arma solo lo que se ve (de ~1.600 controles a ~450); cada panel se arma "
        "la primera vez que lo abrís. «Herramientas» y las barras de desplazamiento ahora se dibujan.",
        "Otro monitor: ya no se pone transparente ni se pega al pasar la ventana a una pantalla con otra escala; "
        "se ajusta una sola vez cuando la soltás.",
        "Organizar: las miniaturas se dibujan en un proceso aparte (la ventana ya no se traba mientras cargan).",
        "Se corrigió un bloqueo ocasional de la ventana (la limpieza de memoria ahora se hace solo en la ventana).",
    ]),
    ("v3.6", [
        "Comparar abre los dos PDF en miniaturas (todas del mismo tamaño, varias por fila). Arrastrá una hoja de "
        "cualquier parte al otro PDF. Ctrl+rueda o − / + las agranda o achica; doble clic ve una hoja grande y otro "
        "doble clic vuelve. Al separar, cada PDF vuelve a como se veía.",
        "Nuevo modo de vista «Miniaturas» (botón de modos de la barra).",
    ]),
    ("v3.5", [
        "Pasar páginas de un PDF a otro desde «Comparar»: cada hoja muestra su número arriba a la derecha. Tomala de "
        "ahí y arrastrala al otro PDF (copia; con Shift la mueve) o a otro lugar del mismo. También Ctrl+C / Ctrl+X / "
        "Ctrl+V, Supr y clic derecho. «Guardar» (Ctrl+S) deja el PDF así o lo guarda como copia.",
        "Se quitó el panel «Otro PDF» de Organizar.",
    ]),
    ("v3.4", [
        "Copiar imágenes del PDF: hacé clic en una foto o imagen del visor (Ctrl+clic para varias) y Ctrl+C. Se pega "
        "como archivo en una carpeta del Explorador, o como imagen en Word, WhatsApp, Paint… Clic derecho: guardar "
        "imagen o copiar todas las de la página.",
    ]),
    ("v3.3", [
        "Girar de verdad desde el visor: con los botones de girar elegís «esta página», «todo el documento» o «solo "
        "la vista». Al guardar (Ctrl+S) el PDF queda girado; Ctrl+Z deshace.",
        "Íconos más nítidos: se dibujan a mayor resolución y respetan la escala de Windows (125 %, 150 %…).",
    ]),
    ("v3.2.2", [
        "Organizar: en «Proceso» elegís qué hacer al procesar (Foliar, Aplanar, Comprimir) y sus ajustes se abren a "
        "la derecha, sin salir de Organizar.",
        "La columna de herramientas de la derecha se ve también en Organizar y en las demás páginas.",
    ]),
    ("v3.2.1", [
        "La columna de herramientas de la derecha dice el nombre de cada una al pasar el mouse (con la pantalla de "
        "Windows al 125 % o 150 % la ayuda quedaba fuera de la ventana).",
    ]),
    ("v3.2", [
        "Diseño como Adobe Acrobat: la hoja ocupa casi toda la pantalla. Arriba solo dos filas finas: Inicio · "
        "Herramientas · documentos, y una barra de íconos chicos (al pasar el mouse dicen qué hacen).",
        "Página, zoom, ajuste, girar y modo de vista en la misma barra, al centro.",
        "A la derecha, una columna de herramientas con sus colores; «Herramientas» las muestra todas en tarjetas.",
        "Los mensajes aparecen un momento abajo a la izquierda de la hoja (ya no hay barra fija abajo).",
        "Las miniaturas empiezan cerradas (se abren con el ícono de la izquierda).",
    ]),
    ("v3.1", [
        "Abre más rápido: la primera hoja la dibuja la ventana apenas aparece, sin esperar a los procesos de dibujo "
        "(en Windows tardaban segundos en arrancar y ahora arrancan después, sin competir con el inicio).",
        "La ventana aparece ya de su tamaño final: la hoja no se ve corrida y después salta.",
        "Si cerrás en pantalla completa o minimizado, la próxima vez abre bien (maximizada o como estaba).",
    ]),
    ("v3.0", [
        "Nueva cara, como Nitro y Adobe (mismos íconos y colores): pestañas de documentos arriba y una cinta con "
        "Inicio · Editar · Organizar · Herramientas · Ver.",
        "Girar la vista en el visor (Girar ← / →): solo cambia cómo se ve, el PDF queda igual.",
        "Vista de una página, continua o dos páginas lado a lado.",
        "Barra de abajo con las páginas, el modo de vista y el zoom (con deslizador).",
        "A la izquierda: miniaturas, marcadores (índice del PDF) y buscar.",
        "Inicio sin documento con los PDF recientes y herramientas a un clic.",
        "Arranque más rápido y corto: una tarjeta quieta que aparece al instante.",
        "Pantalla completa (F11). Al abrir un PDF se ve la página entera (o como la dejaste la última vez).",
        "Organizar: la lista de archivos tiene su propio desplazamiento (ya no se pierde «Procesar»).",
    ]),
    ("v2.8", [
        "Texto: alineación (izquierda, centro, derecha y justificado), subrayado, tachado e interlineado.",
        "Deshacer y rehacer de verdad (Ctrl+Z / Ctrl+Y): agregar, mover, estilo, quitar y cambiar texto, paso a paso.",
        "Duplicar textos, firmas y sellos; las flechas los mueven (Shift: más rápido).",
        "Fondo blanco opcional para tapar lo que hay debajo, y «Otro…» para elegir cualquier color.",
        "Al elegir un texto en la hoja, el panel muestra su fuente, tamaño, color y estilo.",
    ]),
    ("v2.7", [
        "Cambiar texto por párrafo entero (o por renglón, a elección): el texto nuevo se acomoda al ancho del párrafo.",
        "Fuentes: las más comunes de Windows (Arial, Calibri, Times New Roman, Cambria, Verdana, Georgia, Segoe UI y más).",
        "«Cambiar» usa la misma fuente del texto original si está instalada; negrita y cursiva incluidas.",
        "Del PDF guardado solo quedan las letras usadas de cada fuente: el archivo sigue liviano.",
        "Arreglado: al hacer clic en un texto para cambiarlo, la hoja ya no salta a la página 1.",
    ]),
    ("v2.6", [
        "Firmar y sellar: hasta 5 firmas y 5 sellos desde imagen; el fondo blanco se quita solo y queda transparente.",
        "Se usa por defecto la última firma y el último sello que usaste. Se mueven y se cambia el tamaño con el mouse.",
        "Texto: escribí texto nuevo sobre la hoja, o cambiá un texto que ya está en el PDF.",
        "Más liviano: fuera librerías que no se usaban; el proceso de buscar arranca después, así abre más rápido.",
    ]),
    ("v2.5", [
        "PdFOL abre más rápido: la ventana aparece antes y lo que no se ve se arma después.",
        "Al abrir otro documento (también con doble clic en el Explorador) ya no queda la hoja del anterior.",
    ]),
    ("v2.4", [
        "Arreglado el aviso de error (tema_guardado) que salía al abrir PdFOL.",
        "Arrastrá PDF a la ventana: se abren en el visor; en Organizar salen las opciones de «Unir».",
        "Todo archivo que abrís (Abrir, Documento, Organizar, doble clic en el Explorador) cae primero en el visor.",
        "Foliar ya no viene prendido: se prende solo al unir PDF o si lo prendés vos.",
        "Barra de arriba más baja y la barra del visor en la fila de las pestañas: la hoja se ve más grande.",
        "Ícono nítido en la barra de tareas y nuevo ícono para los PDF que abre PdFOL.",
    ]),
    ("v2.3", [
        "Color del tema en Apariencia: Azul gris (el de siempre) o Verde gris, en claro y en oscuro.",
        "Primera versión que se actualiza con el actualizador nuevo (sin ventana negra).",
    ]),
    ("v2.2", [
        "Cierre limpio: al cerrar, PdFOL termina por completo (en Windows podía quedar corriendo escondido).",
        "Actualizador mejorado: no muestra ventana negra y, si PdFOL tarda en cerrarse, lo cierra él.",
        "Las novedades se ven dentro de PdFOL: en «Acerca de», en «Novedades» y al actualizar.",
        "Versión instalada: «Agregar o quitar programas» muestra la versión actual.",
    ]),
    ("v2.1", [
        "Menú del husky: Buscar actualizaciones, Novedades, Ayuda y atajos (F1) y Acerca de.",
        "Puntito naranja sobre el husky cuando hay una versión nueva.",
        "Créditos by Meneses999 en el inicio, el título y «Acerca de».",
    ]),
    ("v2.0", [
        "PdFOL pasa a ser un visor de PDF: pestañas, miniaturas, desplazamiento continuo y zoom.",
        "Buscar (Ctrl+B / Ctrl+F), seleccionar y copiar texto, herramienta Mano.",
        "Resaltador: texto, área o polilínea y libre, con colores; se guarda en el PDF.",
        "Aplanar, Foliar y Comprimir en un panel junto al documento, con el folio en vivo.",
        "Copiar páginas entre pestañas y comparar dos documentos lado a lado.",
        "Imprimir con papel automático (carta, y A3 para los planos) y horizontales paradas.",
        "Organizar con íconos, Rehacer y Ayuda; pregunta si guardar al cerrar.",
        "Animación de inicio, abre maximizado, instalador y actualizaciones desde la app.",
    ]),
]


# =========================================================================
#  PANTALLA DE INICIO: el husky animado mientras se cargan las librerias
#  (es un programa aparte y liviano: aparece enseguida, antes de PyMuPDF)
# =========================================================================
def _pref_guardada(clave, defecto):
    """Lee una preferencia de PdFOL_perfiles.json (lo usa la animacion de inicio, antes de cargar todo)."""
    import json as _json
    base = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) else os.path.dirname(os.path.abspath(__file__))
    for carpeta in (base, os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "PdFOL")):
        try:
            with open(os.path.join(carpeta, "PdFOL_perfiles.json"), encoding="utf-8") as f:
                return _json.load(f).get(clave, defecto)
        except Exception:
            pass
    return defecto


def _apariencia_guardada():
    """'Claro' u 'Oscuro' segun la preferencia guardada (o Windows, si es Automatico)."""
    import json as _json
    base = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) else os.path.dirname(os.path.abspath(__file__))
    modo = "Automático"
    for carpeta in (base, os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "PdFOL")):
        try:
            with open(os.path.join(carpeta, "PdFOL_perfiles.json"), encoding="utf-8") as f:
                modo = _json.load(f).get("apariencia", "Automático")
            break
        except Exception:
            pass
    if modo in ("Claro", "Oscuro"):
        return modo
    if os.name == "nt":
        try:
            import winreg
            k = winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Themes\Personalize")
            return "Claro" if winreg.QueryValueEx(k, "AppsUseLightTheme")[0] else "Oscuro"
        except Exception:
            pass
    return "Claro"


def pantalla_de_inicio():
    """Ventanita con el husky animado. Se cierra cuando PdFOL avisa (cierra la tuberia) o a los 40 s.
    Todo se dibuja suavizado (a 3x y reducido), asi la barra y el texto se ven nitidos."""
    import tkinter as tk
    import base64
    from PIL import Image, ImageDraw, ImageFont, ImageTk
    listo = threading.Event()

    def esperar():
        try:
            sys.stdin.read()  # termina cuando PdFOL cierra la tuberia (o se cierra)
        except Exception:
            pass
        listo.set()
    threading.Thread(target=esperar, daemon=True).start()
    oscuro = _apariencia_guardada() == "Oscuro"
    tarjeta, borde, texto, texto2, acento, suave = (
        ("#232931", "#3A4350", "#E7EBF0", "#9AA6B4", "#7096C8", "#2C333D") if oscuro else
        ("#FFFFFF", "#D9E0E9", "#1E2730", "#6A7685", "#4C6F9F", "#E7ECF3"))
    if _pref_guardada("tema", "Azul gris") == "Verde gris":
        tarjeta, borde, texto, texto2, acento, suave = (
            ("#232A27", "#3A4640", "#E6ECE8", "#9FB0A6", "#9FB0A6", "#2C3531") if oscuro else
            ("#FFFFFF", "#D5DFD9", "#1F2A25", "#66766D", "#5F7D6C", "#E5EDE8"))

    def hx(c_):
        c_ = c_.lstrip("#")
        return tuple(int(c_[i:i + 2], 16) for i in (0, 2, 4))

    def fuente(tam, negrita=False):
        nombres = (["segoeuib.ttf", "seguisb.ttf"] if negrita else ["segoeui.ttf"]) + \
                  (["DejaVuSans-Bold.ttf"] if negrita else ["DejaVuSans.ttf"])
        for n_ in nombres:
            for base in ("", os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts"),
                         "/usr/share/fonts/truetype/dejavu"):
                try:
                    return ImageFont.truetype(os.path.join(base, n_) if base else n_, tam)
                except Exception:
                    pass
        try:
            return ImageFont.load_default(tam)
        except Exception:
            return ImageFont.load_default()

    W, H, K = 340, 336, 3  # K: dibujo a 3x y reduzco (suavizado)
    r = tk.Tk()
    r.overrideredirect(True)
    r.attributes("-topmost", True)
    sx, sy = r.winfo_screenwidth(), r.winfo_screenheight()
    r.geometry(f"{W}x{H}+{(sx - W) // 2}+{(sy - H) // 2 - 40}")
    r.configure(bg=tarjeta)
    cv = tk.Canvas(r, width=W, height=H, highlightthickness=0, bd=0, bg=tarjeta)
    cv.pack()
    # fondo fijo: tarjeta con borde, nombre y version (nitidos)
    fondo = Image.new("RGB", (W * K, H * K), hx(tarjeta))
    d = ImageDraw.Draw(fondo)
    d.rectangle([0, 0, W * K - 1, H * K - 1], outline=hx(borde), width=K)
    f1, f2, f3 = fuente(27 * K, True), fuente(14 * K, True), fuente(11 * K)
    w1 = d.textlength(NOMBRE, font=f1)
    w2 = d.textlength(VERSION, font=f2)
    x0 = (W * K - (w1 + 7 * K + w2)) / 2
    d.text((x0, 182 * K), NOMBRE, font=f1, fill=hx(texto))
    d.text((x0 + w1 + 7 * K, 193 * K), VERSION, font=f2, fill=hx(acento))
    sub = "Aplanar · Foliar · Comprimir"
    d.text(((W * K - d.textlength(sub, font=f3)) / 2, 216 * K), sub, font=f3, fill=hx(texto2))
    f4 = fuente(10 * K, True)
    autor = f"by {AUTOR}"
    d.text(((W * K - d.textlength(autor, font=f4)) / 2, 234 * K), autor, font=f4, fill=hx(acento))
    fondo = fondo.resize((W, H), Image.LANCZOS)
    husky = Image.open(io.BytesIO(base64.b64decode("".join(ICONO_PNG_B64)))).convert("RGBA").resize((128, 128),
                                                                                                       Image.LANCZOS)
    # barra (pastilla) y textos animados, a 3x
    BX, BY, BW, BH = 80, 306, W - 160, 6
    fA = fuente(11 * K)

    def cuadro(t):
        im = fondo.copy()
        rebote = abs(math.sin(t * 3.2))  # el husky salta suave
        # sombra que se achica cuando sube
        sw_ = int(70 - 26 * rebote)
        som = Image.new("RGBA", (sw_ * K, 10 * K), (0, 0, 0, 0))
        ImageDraw.Draw(som).ellipse([0, 0, sw_ * K - 1, 10 * K - 1], fill=hx(suave) + (255,))
        som = som.resize((sw_, 10), Image.LANCZOS)
        im.paste(som, ((W - sw_) // 2, 166), som)
        im.paste(husky, ((W - 128) // 2, int(36 - 16 * rebote)), husky)
        # barra
        b_ = Image.new("RGBA", (BW * K, BH * K), (0, 0, 0, 0))
        db = ImageDraw.Draw(b_)
        db.rounded_rectangle([0, 0, BW * K - 1, BH * K - 1], radius=BH * K // 2, fill=hx(suave) + (255,))
        ancho = 64
        pos = (t * 150) % (BW + ancho) - ancho
        a_, z_ = max(0, pos), min(BW, pos + ancho)
        if z_ - a_ > 2:
            db.rounded_rectangle([a_ * K, 0, z_ * K - 1, BH * K - 1], radius=BH * K // 2, fill=hx(acento) + (255,))
        b_ = b_.resize((BW, BH), Image.LANCZOS)
        im.paste(b_, (BX, BY), b_)
        return im

    # «Abriendo…» con puntos que laten (texto Tk nativo, ya suavizado por Windows)
    fam = "Segoe UI" if os.name == "nt" else "DejaVu Sans"
    foto = {"img": None}
    item = cv.create_image(0, 0, anchor="nw")
    lbl = cv.create_text(W / 2 - 6, 282, text="", font=(fam, 10), fill=texto2)
    puntos = [cv.create_text(0, 282, text="•", font=(fam, 9), fill=texto2) for _ in range(3)]
    import tkinter.font as tkf
    fl = tkf.Font(family=fam, size=10)
    base_txt = "Abriendo"
    wl = fl.measure(base_txt)
    cv.itemconfigure(lbl, text=base_txt)
    for k_, p_ in enumerate(puntos):
        cv.coords(p_, W / 2 - 6 + wl / 2 + 7 + k_ * 7, 283)
    c2, c1 = hx(texto2), hx(tarjeta)
    t0 = time.time()

    def paso():
        if listo.is_set() or time.time() - t0 > 40:
            r.destroy()
            return
        t = time.time() - t0
        foto["img"] = ImageTk.PhotoImage(cuadro(t))
        cv.itemconfigure(item, image=foto["img"])
        cv.tag_raise(lbl)
        for k_, p_ in enumerate(puntos):  # cada punto se enciende y se apaga, uno tras otro
            a_ = (math.sin(t * 5 - k_ * 0.9) + 1) / 2
            cv.tag_raise(p_)
            cv.itemconfigure(p_, fill="#%02x%02x%02x" % tuple(int(c1[i] + (c2[i] - c1[i]) * a_) for i in range(3)))
        r.after(25, paso)

    def redondear():
        if os.name == "nt":  # Windows 11: esquinas redondeadas nativas
            try:
                import ctypes
                hwnd = ctypes.windll.user32.GetParent(r.winfo_id()) or r.winfo_id()
                v_ = ctypes.c_int(2)
                ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 33, ctypes.byref(v_), ctypes.sizeof(v_))
            except Exception:
                pass
    r.after(1, redondear)
    r.after(5, paso)
    r.mainloop()


def lanzar_pantalla_de_inicio():
    """Abre la pantalla de inicio en otro proceso (sin consola). Devuelve el proceso o None."""
    import subprocess
    try:
        cmd = [sys.executable] + ([] if getattr(sys, "frozen", False) else [os.path.abspath(__file__)]) + ["--pdfol-inicio"]
        return subprocess.Popen(cmd, stdin=subprocess.PIPE, creationflags=0x08000000 if os.name == "nt" else 0)
    except Exception:
        return None


def crear_imagen_inicio(destino):
    """v3.0: la tarjeta de inicio que muestra el .exe al instante (PyInstaller --splash), antes de Python."""
    from PIL import Image, ImageDraw, ImageFont
    W, H, K = 360, 150, 3
    im = Image.new("RGB", (W * K, H * K), (255, 255, 255))
    d = ImageDraw.Draw(im)
    d.rectangle([0, 0, W * K - 1, H * K - 1], outline=(217, 224, 233), width=K * 2)

    def fuente(tam, negrita=False):
        for n_ in ((["segoeuib.ttf", "DejaVuSans-Bold.ttf"] if negrita else ["segoeui.ttf", "DejaVuSans.ttf"])):
            for base in ("", os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts"),
                         "/usr/share/fonts/truetype/dejavu"):
                try:
                    return ImageFont.truetype(os.path.join(base, n_) if base else n_, tam)
                except Exception:
                    pass
        return ImageFont.load_default()
    husky = icono_husky(84 * K).convert("RGBA")
    im.paste(husky, (34 * K, (H * K - husky.height) // 2), husky)
    f1, f2, f3 = fuente(30 * K, True), fuente(14 * K, True), fuente(11 * K)
    x0 = 140 * K
    d.text((x0, 38 * K), NOMBRE, font=f1, fill=(30, 39, 48))
    w1 = d.textlength(NOMBRE, font=f1)
    d.text((x0 + w1 + 8 * K, 51 * K), VERSION, font=f2, fill=(76, 111, 159))
    d.text((x0 + 2 * K, 84 * K), f"by {AUTOR}", font=f3, fill=(106, 118, 133))
    d.text((x0 + 2 * K, 104 * K), "Abriendo…", font=f3, fill=(106, 118, 133))
    im.resize((W, H), Image.LANCZOS).save(destino)


def cerrar_pantalla_de_inicio():
    global _INICIO
    try:  # v3.0: la tarjeta del .exe (PyInstaller) se cierra apenas aparece la ventana
        import pyi_splash
        pyi_splash.close()
    except Exception:
        pass
    if _INICIO is not None:
        try:
            _INICIO.stdin.close()
        except Exception:
            pass
        _INICIO = None


_INICIO = None
if __name__ == "__main__":
    if "--pdfol-inicio" in sys.argv:
        try:
            pantalla_de_inicio()
        except BaseException:  # la animacion es un adorno: si falla, no se muestra nada
            if os.environ.get("PDFOL_AUTOPRUEBA"):  # pero en la prueba automatica se anota el error
                import traceback
                with open(os.environ.get("PDFOL_AUTOPRUEBA_LOG", "pdfol_autoprueba.log"), "a", encoding="utf-8") as f_:
                    f_.write("PANTALLA DE INICIO\n" + traceback.format_exc())
                os._exit(3)
        os._exit(0)
    if (not any(a.startswith("--") for a in sys.argv[1:]) and not os.environ.get("PDFOL_PRUEBA")
            and not os.environ.get("PDFOL_SIN_INICIO") and not getattr(sys, "frozen", False)
            and os.environ.get("PDFOL_INICIO_ANIMADO")):
        # v3.0: el .exe ya muestra su tarjeta al instante; la animacion queda solo a pedido (PDFOL_INICIO_ANIMADO)
        _INICIO = lanzar_pantalla_de_inicio()  # la ventana de PdFOL todavia tarda: el husky aparece ya


import pymupdf as fitz


class _Perezoso:
    """v2.5: importa la libreria recien la primera vez que se usa (el arranque es mas rapido)."""

    def __init__(self, modulo, attr=None):
        self._modulo, self._attr, self._obj = modulo, attr, None

    def _cargar(self):
        if self._obj is None:
            import importlib
            m = importlib.import_module(self._modulo)
            self._obj = getattr(m, self._attr) if self._attr else m
        return self._obj

    def __getattr__(self, a):
        return getattr(self._cargar(), a)

    def __call__(self, *a, **k):
        return self._cargar()(*a, **k)


pikepdf = _Perezoso("pikepdf")
Name = _Perezoso("pikepdf", "Name")
from PIL import Image, ImageChops, ImageDraw

Image.MAX_IMAGE_PIXELS = None

DPI_DEFECTO = 400
CALIDAD_JPEG = 92
MOSAICO = 512


class Cancelado(Exception):
    pass


def fmt_tiempo(seg):
    seg = max(0, int(seg))
    m, s = divmod(seg, 60)
    h, m = divmod(m, 60)
    return f"{h} h {m:02d} min" if h else (f"{m} min {s:02d} s" if m else f"{s} s")


def parsear_paginas(texto, n):
    res = set()
    for parte in (texto or "").replace(";", ",").split(","):
        parte = parte.strip()
        if not parte:
            continue
        if "-" in parte:
            a, b = parte.split("-", 1)
            res.update(p - 1 for p in range(int(a), int(b) + 1) if 1 <= p <= n)
        elif 1 <= int(parte) <= n:
            res.add(int(parte) - 1)
    return res


# =========================================================================
#  ANALISIS (deteccion de planos pesados)
# =========================================================================
def _complejidad(doc, page):
    vistos, total = set(), 0
    for x in page.get_contents():
        if x not in vistos:
            vistos.add(x)
            try:
                total += len(doc.xref_stream(x) or b"")
            except Exception:
                pass
    try:
        xobjs = page.get_xobjects()
    except Exception:
        xobjs = []
    for item in xobjs:
        x = item[0]
        if x and x not in vistos:
            vistos.add(x)
            try:
                total += len(doc.xref_stream(x) or b"")
            except Exception:
                pass
    return total


def analizar(ruta, progreso=None, cancelar=None):
    """Devuelve (KB de vectores por pagina, umbral KB sugerido)."""
    fitz.TOOLS.mupdf_display_errors(False)
    doc = fitz.open(ruta)
    n = doc.page_count
    scores = []
    for i in range(n):
        if cancelar is not None and cancelar.is_set():
            doc.close()
            raise Cancelado()
        scores.append(_complejidad(doc, doc[i]) / 1024)
        if progreso and (i % 25 == 0 or i == n - 1):
            progreso(i + 1, n)
    doc.close()
    mediana = statistics.median(scores) if scores else 0
    return scores, max(300.0, mediana * 5)


def contar_paginas(ruta):
    fitz.TOOLS.mupdf_display_errors(False)
    with fitz.open(ruta) as d:
        return d.page_count


# =========================================================================
#  FOLIADO
# =========================================================================
def carpeta_recursos():
    """Carpeta de recursos (fuentes incluidas): junto al .py o dentro del .exe."""
    return getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))


# nombre: (archivo normal, archivo negrita, interna normal, interna negrita, incluida_en_programa)
FUENTES = {
    # --- estilo foliador / sello / maquina de escribir (incluidas en el programa)
    "Special Elite (sello)": ("SpecialElite-Regular.ttf", None, "cour", "cobo", True),
    "Courier Prime": ("CourierPrime-Regular.ttf", "CourierPrime-Bold.ttf", "cour", "cobo", True),
    "Cutive Mono": ("CutiveMono-Regular.ttf", None, "cour", "cobo", True),
    "IBM Plex Mono": ("IBMPlexMono-Regular.ttf", "IBMPlexMono-Bold.ttf", "cour", "cobo", True),
    "Share Tech Mono": ("ShareTechMono-Regular.ttf", None, "cour", "cobo", True),
    "Stardos Stencil": ("StardosStencil-Regular.ttf", "StardosStencil-Bold.ttf", "tiro", "tibo", True),
    "Allerta Stencil": ("AllertaStencil-Regular.ttf", None, "helv", "hebo", True),
    "Black Ops One": ("BlackOpsOne-Regular.ttf", None, "hebo", "hebo", True),
    # --- fuentes de Windows
    "Arial": ("arial.ttf", "arialbd.ttf", "helv", "hebo", False),
    "Times New Roman": ("times.ttf", "timesbd.ttf", "tiro", "tibo", False),
    "Calibri": ("calibri.ttf", "calibrib.ttf", "helv", "hebo", False),
    "Cambria": ("cambria.ttc", "cambriab.ttf", "tiro", "tibo", False),
    "Courier New": ("cour.ttf", "courbd.ttf", "cour", "cobo", False),
    "Verdana": ("verdana.ttf", "verdanab.ttf", "helv", "hebo", False),
    "Tahoma": ("tahoma.ttf", "tahomabd.ttf", "helv", "hebo", False),
    "Segoe UI": ("segoeui.ttf", "segoeuib.ttf", "helv", "hebo", False),
    "Century Gothic": ("GOTHIC.TTF", "GOTHICB.TTF", "helv", "hebo", False),
    "Georgia": ("georgia.ttf", "georgiab.ttf", "tiro", "tibo", False),
    # --- internas (siempre disponibles)
    "Helvetica (interna)": (None, None, "helv", "hebo", False),
    "Times (interna)": (None, None, "tiro", "tibo", False),
    "Courier (interna)": (None, None, "cour", "cobo", False),
}
POSICIONES = {
    "Abajo derecha": ("abajo", "der"),
    "Abajo centro": ("abajo", "centro"),
    "Abajo izquierda": ("abajo", "izq"),
    "Arriba derecha": ("arriba", "der"),
    "Arriba centro": ("arriba", "centro"),
    "Arriba izquierda": ("arriba", "izq"),
}


def _carpeta_fuentes():
    return os.path.join(os.environ.get("WINDIR", r"C:\Windows"), "Fonts")


def _buscar_archivo_fuente(nombre_archivo, incluida=False):
    if not nombre_archivo:
        return None
    if incluida:
        p = os.path.join(carpeta_recursos(), "fuentes", nombre_archivo)
        return p if os.path.isfile(p) else None
    carpetas = [_carpeta_fuentes(),
                os.path.join(os.environ.get("LOCALAPPDATA", ""), "Microsoft", "Windows", "Fonts")]
    for c in carpetas:
        p = os.path.join(c, nombre_archivo)
        if os.path.isfile(p):
            return p
        try:  # busqueda sin distinguir mayusculas
            for f in os.listdir(c):
                if f.lower() == nombre_archivo.lower():
                    return os.path.join(c, f)
        except Exception:
            pass
    return None


def fuentes_disponibles():
    """Fuentes de Windows instaladas + las internas (siempre disponibles)."""
    res = []
    for nombre, (a, _, _, _, inc) in FUENTES.items():
        if a is None or _buscar_archivo_fuente(a, inc):
            res.append(nombre)
    return res


_CACHE_FUENTE = {}


def _resolver_fuente(nombre, negrita):
    """Devuelve (archivo o None, nombre interno, objeto fitz.Font, negrita_simulada)."""
    clave = (nombre, negrita)
    if clave in _CACHE_FUENTE:
        return _CACHE_FUENTE[clave]
    a, ab, i, ib, inc = FUENTES.get(nombre, FUENTES["Helvetica (interna)"])
    simulada = False
    archivo = None
    if negrita:
        archivo = _buscar_archivo_fuente(ab, inc)
        if archivo is None and a:
            # la fuente no trae version negrita: se usa la normal con trazo
            archivo = _buscar_archivo_fuente(a, inc)
            simulada = archivo is not None
    else:
        archivo = _buscar_archivo_fuente(a, inc)
    interna = ib if negrita else i
    try:
        font = fitz.Font(fontfile=archivo) if archivo else fitz.Font(interna)
    except Exception:
        archivo, simulada, font = None, False, fitz.Font(interna)
    _CACHE_FUENTE[clave] = (archivo, interna, font, simulada)
    return _CACHE_FUENTE[clave]


def folio_por_defecto():
    return {
        "inicio": 1, "digitos": 4, "desde": 1, "hasta": None,
        "con_total": False, "prefijo": "Folio",
        "fuente": "Special Elite (sello)", "tam": 12.0, "negrita": False,
        "color": (0, 0, 0), "posicion": "Abajo derecha", "margen_h_mm": 10.0, "margen_v_mm": 10.0,
    }


def texto_folio(cfg, numero, total):
    d = max(1, int(cfg["digitos"]))
    s = str(numero).zfill(d)
    if cfg["con_total"]:
        s += " / " + str(total).zfill(d)
    pre = (cfg.get("prefijo") or "").strip()
    return f"{pre} {s}" if pre else s


def rango_folio(cfg, n_paginas):
    """Indices (0-based) de las paginas a foliar."""
    desde = max(1, int(cfg["desde"]))
    hasta = int(cfg["hasta"]) if cfg.get("hasta") else n_paginas
    hasta = min(hasta, n_paginas)
    return list(range(desde - 1, hasta))


CARTA = (612.0, 792.0)   # 8.5 x 11 pulgadas
A3 = (841.9, 1190.6)     # 297 x 420 mm


def papel_fisico(ancho, alto):
    """Papel en que se imprime la pagina (siempre parada) y factor pagina -> papel.
    Carta, oficio, A4 o parecido -> carta. Mas grande (planos) -> A3."""
    corto, largo = min(ancho, alto), max(ancho, alto)
    papel = CARTA if (largo <= 1100 and corto <= 800) else A3
    f = min(papel[0] / max(corto, 1), papel[1] / max(largo, 1))
    return ("Carta" if papel is CARTA else "A3"), f


def estampar_folio(page, texto, cfg):
    """Escribe el folio en una pagina de PyMuPDF como se vera IMPRESO:
    - mismo tamano y margenes en papel en todas las hojas (la pagina se imprime ajustada a carta,
      o a A3 si es un plano grande), asi que en el PDF el numero se escala por pagina;
    - las paginas horizontales se archivan paradas con el encabezado hacia la perforacion
      (izquierda): el folio va en la misma esquina fisica y se lee derecho con la hoja parada.
    margen_h_mm / margen_v_mm: distancias en el papel. Devuelve el rectangulo del texto
    en coordenadas visibles de la pagina."""
    archivo, interna, font, simulada = _resolver_fuente(cfg["fuente"], cfg["negrita"])
    R = page.rect
    W, H = R.width, R.height
    _, f = papel_fisico(W, H)
    k = 1.0 / f  # unidades de la pagina por punto de papel
    tam = float(cfg["tam"]) * k
    mh = float(cfg.get("margen_h_mm", cfg.get("margen_mm", 10))) * 72 / 25.4 * k
    mv = float(cfg.get("margen_v_mm", cfg.get("margen_mm", 10))) * 72 / 25.4 * k
    acostada = W > H * 1.001
    Pw, Ph = (H, W) if acostada else (W, H)  # hoja fisica parada
    tw = font.text_length(texto, fontsize=tam)
    asc, desc = font.ascender * tam, font.descender * tam
    vert, horiz = POSICIONES.get(cfg["posicion"], ("abajo", "der"))
    if horiz == "izq":
        px = mh
    elif horiz == "centro":
        px = (Pw - tw) / 2 + mh
    else:
        px = Pw - mh - tw
    py = mv + asc if vert == "arriba" else Ph - mv + desc
    if acostada:
        # hoja parada = pagina girada 90 grados a la izquierda (arriba -> lado izquierdo)
        x, y = R.x0 + W - py, R.y0 + px
        giro = 270
        caja = fitz.Rect(R.x0 + W - (py - desc), R.y0 + px, R.x0 + W - (py - asc), R.y0 + px + tw)
    else:
        x, y = R.x0 + px, R.y0 + py
        giro = 0
        caja = fitz.Rect(x, y - asc, x + tw, y - desc)
    punto = fitz.Point(x, y) * page.derotation_matrix
    rot = (page.rotation + giro) % 360
    color = tuple(c / 255 for c in cfg["color"])
    extra = {}
    if simulada:  # negrita simulada: relleno + trazo del mismo color
        extra = dict(render_mode=2, fill=color, border_width=0.035)
    if archivo:
        nombre = "PdFOL" + hashlib.md5(archivo.encode("utf-8")).hexdigest()[:8]
        page.insert_text(punto, texto, fontsize=tam, fontname=nombre, fontfile=archivo,
                         color=color, rotate=rot, **extra)
    else:
        page.insert_text(punto, texto, fontsize=tam, fontname=interna, color=color, rotate=rot, **extra)
    return caja


def _heredado(obj, clave):
    o = obj
    for _ in range(30):
        if o is None:
            return None
        if clave in o:
            return o[clave]
        o = o.get("/Parent")
    return None


def aplicar_folios(pdf, cfg, estado=None, cancelar=None):
    """Agrega los folios al PDF abierto con pikepdf (como capa vectorial)."""
    estado = estado or (lambda m: None)
    n = len(pdf.pages)
    indices = rango_folio(cfg, n)
    if not indices:
        return 0
    inicio = int(cfg["inicio"])
    total = inicio + len(indices) - 1
    estado(f"Foliando {len(indices)} páginas...")
    fdoc = fitz.open()
    for k, i in enumerate(indices):
        po = pdf.pages[i].obj
        mb = _heredado(po, "/MediaBox")
        cb = _heredado(po, "/CropBox") or mb
        rot = int(_heredado(po, "/Rotate") or 0) % 360
        fp = fdoc.new_page()
        fdoc.xref_set_key(fp.xref, "MediaBox", "[" + " ".join(f"{float(v):g}" for v in mb) + "]")
        fdoc.xref_set_key(fp.xref, "CropBox", "[" + " ".join(f"{float(v):g}" for v in cb) + "]")
        if rot:
            fdoc.xref_set_key(fp.xref, "Rotate", str(rot))
        fp = fdoc.reload_page(fp)
        estampar_folio(fp, texto_folio(cfg, inicio + k, total), cfg)
        if cancelar is not None and k % 200 == 0 and cancelar.is_set():
            raise Cancelado()
    try:
        fdoc.subset_fonts()
    except Exception:
        pass
    fpdf = pikepdf.open(io.BytesIO(fdoc.tobytes(garbage=3, deflate=True)))
    fdoc.close()
    for k, i in enumerate(indices):
        form = fpdf.pages[k].as_form_xobject(handle_transformations=False)
        if not form.is_indirect:
            form = fpdf.make_indirect(form)
        pagina = pdf.pages[i]
        nombre = pagina.add_resource(pdf.copy_foreign(form), Name.XObject, prefix="PdFOL")
        pagina.contents_add(pdf.make_stream(b"q\n"), prepend=True)
        pagina.contents_add(pdf.make_stream(b"\nQ q " + str(nombre).encode() + b" Do Q\n"))
    return len(indices)


# =========================================================================
#  APLANAR: trabajo en cada nucleo
# =========================================================================
_DOC = None
_COLA = None
_FUENTE_TXT = None
_BLANCO = ((255, 255), (255, 255), (255, 255))


def _iniciar_trabajador(ruta, cola):
    global _DOC, _COLA, _FUENTE_TXT
    if sys.stdout is None:
        sys.stdout = open(os.devnull, "w")
    if sys.stderr is None:
        sys.stderr = open(os.devnull, "w")
    fitz.TOOLS.mupdf_display_errors(False)
    _DOC = fitz.open(ruta)
    _COLA = cola
    _FUENTE_TXT = fitz.Font("helv")


def _texto_invisible(origen, destino):
    try:
        palabras = origen.get_text("words")
    except Exception:
        return
    if not palabras:
        return
    rot = origen.rotation_matrix
    tw = fitz.TextWriter(destino.rect)
    verticales = []
    for x0, y0, x1, y1, palabra, *_ in palabras:
        r = fitz.Rect(x0, y0, x1, y1) * rot
        alto, ancho = r.height, r.width
        if alto <= 0 or ancho <= 0:
            continue
        if alto > ancho * 1.5 and len(palabra) > 1:
            verticales.append((r, palabra))
            continue
        tam = alto * 0.85
        if tam < 1:
            continue
        try:
            tw.append((r.x0, r.y1 - alto * 0.2), palabra, font=_FUENTE_TXT, fontsize=tam)
        except Exception:
            pass
    try:
        tw.write_text(destino, render_mode=3)
    except Exception:
        pass
    for r, palabra in verticales:
        tam = r.width * 0.85
        if tam < 1:
            continue
        try:
            p = fitz.Point(r.x1 - r.width * 0.2, r.y1)
            tv = fitz.TextWriter(destino.rect)
            tv.append(p, palabra, font=_FUENTE_TXT, fontsize=tam)
            tv.write_text(destino, render_mode=3, morph=(p, fitz.Matrix(-90)))
        except Exception:
            pass


def _es_gris(tile):
    """True si TODOS los pixeles son grises exactos (R=G=B)."""
    r, g, b = tile.split()
    return ImageChops.difference(r, g).getbbox() is None and ImageChops.difference(g, b).getbbox() is None


def _rasterizar(page, out, dpi, calidad, texto):
    """Dibuja la pagina por franjas y la guarda como mosaicos JPEG.
    Mosaicos totalmente blancos: no se guardan. Mosaicos sin color: en grises."""
    r = page.rect
    escala = dpi / 72.0
    mat = fitz.Matrix(escala, escala)
    dl = page.get_displaylist(annots=True)
    W = int(round(r.width * escala))
    H = int(round(r.height * escala))
    sx, sy = r.width / W, r.height / H
    alto_pt = r.height
    nueva = out.new_page(width=r.width, height=r.height)
    filas = max(1, int(120 * 1048576 // max(1, W * 3 * MOSAICO)))
    alto_franja = MOSAICO * min(filas, 16)
    recursos, ops = [], ["q"]
    k = 0
    for fy in range(0, H, alto_franja):
        fy2 = min(fy + alto_franja, H)
        clip = fitz.Rect(r.x0, r.y0 + fy * sy, r.x1, r.y0 + fy2 * sy)
        franja = dl.get_pixmap(matrix=mat, alpha=False, clip=clip)
        if franja.n != 3:
            franja = fitz.Pixmap(fitz.csRGB, franja)
        ox, oy, fw, fh = franja.x, franja.y, franja.width, franja.height
        img = Image.frombuffer("RGB", (fw, fh), franja.samples, "raw", "RGB", 0, 1)
        for y in range(0, fh, MOSAICO):
            for x in range(0, fw, MOSAICO):
                x2, y2 = min(x + MOSAICO, fw), min(y + MOSAICO, fh)
                tile = img.crop((x, y, x2, y2))
                if tile.getextrema() == _BLANCO:
                    continue
                # Grises exactos -> 1 canal (identico). Luego se prueban dos
                # codificaciones y se guarda la mas liviana:
                #   Flate: SIN PERDIDA (ideal para lineas de planos)
                #   JPEG : mejor para fotos y degradados
                if _es_gris(tile):
                    tile = tile.convert("L")
                    cs = "/DeviceGray"
                else:
                    cs = "/DeviceRGB"
                exacto = zlib.compress(tile.tobytes(), 6)
                buf = io.BytesIO()
                if cs == "/DeviceGray":
                    tile.save(buf, "JPEG", quality=calidad)
                else:
                    tile.save(buf, "JPEG", quality=calidad, subsampling=0)
                jpg = buf.getvalue()
                if len(exacto) <= len(jpg):
                    data, filtro = exacto, "/FlateDecode"
                else:
                    data, filtro = jpg, "/DCTDecode"
                w, h = x2 - x, y2 - y
                xref = out.get_new_xref()
                out.update_object(xref, f"<</Type/XObject/Subtype/Image/Width {w}/Height {h}"
                                        f"/ColorSpace{cs}/BitsPerComponent 8/Filter{filtro}>>")
                out.update_stream(xref, data, compress=0)
                out.xref_set_key(xref, "Filter", filtro)
                nombre = f"M{k}"
                recursos.append(f"/{nombre} {xref} 0 R")
                px0, py0 = (ox + x) * sx, (oy + y) * sy
                pw, ph = w * sx, h * sy
                ops.append(f"q {pw:.4f} 0 0 {ph:.4f} {px0:.4f} {alto_pt - py0 - ph:.4f} cm /{nombre} Do Q")
                k += 1
        img = None
        franja = None
    dl = None
    ops.append("Q")
    out.xref_set_key(nueva.xref, "Resources", "<</XObject<<" + "".join(recursos) + ">>>>")
    cxref = out.get_new_xref()
    out.update_object(cxref, "<<>>")
    out.update_stream(cxref, "\n".join(ops).encode())
    out.xref_set_key(nueva.xref, "Contents", f"{cxref} 0 R")
    if texto:
        _texto_invisible(page, nueva)


def _trabajar(bloque_id, paginas, dpi, calidad, texto, carpeta_tmp):
    out = fitz.open()
    for i in paginas:
        _rasterizar(_DOC[i], out, dpi, calidad, texto)
        _COLA.put(i)
    ruta = os.path.join(carpeta_tmp, f"bloque_{bloque_id:05d}.pdf")
    out.save(ruta, garbage=1, deflate=True)
    out.close()
    return bloque_id, paginas, ruta


_CAJAS = ("/CropBox", "/TrimBox", "/BleedBox", "/ArtBox", "/Rotate",
          "/UserUnit", "/Group", "/Thumb", "/PieceInfo", "/VP")


def _reemplazar_pagina(pdf, pagina, tmp_pdf, tmp_pagina):
    """Pone el plano aplanado dentro de la MISMA pagina del original."""
    po, to = pagina.obj, tmp_pagina.obj
    mb = [float(v) for v in _heredado(po, "/MediaBox")]
    cb = _heredado(po, "/CropBox")
    sin_cambio = (int(_heredado(po, "/Rotate") or 0) % 360 == 0 and mb[0] == 0 and mb[1] == 0
                  and (cb is None or [float(v) for v in cb] == mb))
    for k in _CAJAS:
        if k in po:
            del po[k]
    po.Rotate = 0  # por si la rotacion venia heredada
    po.MediaBox = pikepdf.Array([float(v) for v in to.MediaBox])

    def traer(obj):
        if not obj.is_indirect:
            obj = tmp_pdf.make_indirect(obj)
        return pdf.copy_foreign(obj)

    po.Contents = traer(to.Contents)
    po.Resources = traer(to.Resources)
    if "/Annots" in po:
        quedan = pikepdf.Array()
        if sin_cambio:
            for a in po.Annots:
                try:
                    if a.get("/Subtype") == Name.Link:
                        quedan.append(a)
                except Exception:
                    pass
        if len(quedan):
            po.Annots = quedan
        else:
            del po["/Annots"]


def memoria_libre_mb():
    try:
        if os.name == "nt":
            import ctypes

            class MS(ctypes.Structure):
                _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong),
                            ("ullTotalPhys", ctypes.c_ulonglong), ("ullAvailPhys", ctypes.c_ulonglong),
                            ("ullTotalPageFile", ctypes.c_ulonglong), ("ullAvailPageFile", ctypes.c_ulonglong),
                            ("ullTotalVirtual", ctypes.c_ulonglong), ("ullAvailVirtual", ctypes.c_ulonglong),
                            ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]
            m = MS()
            m.dwLength = ctypes.sizeof(MS)
            ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m))
            return m.ullAvailPhys // 1048576
        return os.sysconf("SC_AVPHYS_PAGES") * os.sysconf("SC_PAGE_SIZE") // 1048576
    except Exception:
        return 4096


def nucleos_recomendados(dpi):
    cpus = os.cpu_count() or 2
    por_nucleo = 120 + (dpi / 400) ** 2 * 230
    por_ram = int(max(1, (memoria_libre_mb() - 1024) // por_nucleo))
    return max(1, min(cpus - 1 if cpus > 2 else cpus, por_ram, 16))


# =========================================================================
#  COMPRIMIR (sin bajar resolucion)
# =========================================================================
NIVELES = {"sin-perdida": None, "equilibrada": 85, "alta": 75}
NOMBRES_NIVEL = {"sin-perdida": "Sin pérdida", "equilibrada": "Equilibrada", "alta": "Alta"}
CALIDAD_MOSAICO = {None: CALIDAD_JPEG, "sin-perdida": CALIDAD_JPEG, "equilibrada": 85, "alta": 75}


def _componentes(cs):
    try:
        if isinstance(cs, pikepdf.Name):
            return {"/DeviceRGB": 3, "/DeviceGray": 1, "/CalRGB": 3, "/CalGray": 1}.get(str(cs))
        if isinstance(cs, pikepdf.Array) and len(cs) >= 2:
            tipo = str(cs[0])
            if tipo == "/ICCBased":
                n = int(cs[1].get("/N", 0))
                return n if n in (1, 3) else None
            if tipo in ("/CalRGB", "/CalGray"):
                return 3 if tipo == "/CalRGB" else 1
    except Exception:
        pass
    return None


def _recomprimir_imagen(img, calidad):
    try:
        if img.get("/ImageMask", False) or "/Mask" in img or "/Decode" in img:
            return 0
        if int(img.get("/BitsPerComponent", 8)) != 8:
            return 0
        w, h = int(img.Width), int(img.Height)
        if w * h < 150 * 150:
            return 0
        filtros = img.get("/Filter")
        nombres = [str(f) for f in filtros] if isinstance(filtros, pikepdf.Array) else \
                  ([str(filtros)] if filtros is not None else [])
        if any(f in ("/JPXDecode", "/JBIG2Decode", "/CCITTFaxDecode") for f in nombres):
            return 0
        n = _componentes(img.get("/ColorSpace"))
        if n is None:
            return 0
        antes = len(img.read_raw_bytes())
        pil = pikepdf.PdfImage(img).as_pil_image().convert("RGB" if n == 3 else "L")
        buf = io.BytesIO()
        pil.save(buf, "JPEG", quality=calidad, subsampling=0 if calidad >= 85 else 1, optimize=True)
        datos = buf.getvalue()
        if len(datos) >= antes * 0.9:
            return 0
        img.write(datos, filter=Name.DCTDecode)
        if "/DecodeParms" in img:
            del img["/DecodeParms"]
        img.BitsPerComponent = 8
        return antes - len(datos)
    except Exception:
        return 0


def _recorrer_xobjects(recursos, visitar, vistos, nivel=0):
    if recursos is None or nivel > 12:
        return
    try:
        xobjs = recursos.get("/XObject")
    except Exception:
        return
    if xobjs is None:
        return
    for nombre in list(xobjs.keys()):
        xo = xobjs[nombre]
        if not isinstance(xo, pikepdf.Stream):
            continue
        sub = xo.get("/Subtype")
        if sub == Name.Image:
            visitar(xobjs, nombre, xo)
        elif sub == Name.Form and xo.objgen not in vistos:
            vistos.add(xo.objgen)
            _recorrer_xobjects(xo.get("/Resources"), visitar, vistos, nivel + 1)


def comprimir_pdf(pdf, nivel, omitir=(), estado=None, cancelar=None):
    estado = estado or (lambda m: None)
    calidad = NIVELES.get(nivel)
    omitir = set(omitir)
    hechas, huellas, vistos_form = set(), {}, set()
    total = len(pdf.pages)

    def visitar(xobjs, nombre, img):
        og = img.objgen
        if og in hechas:
            return
        try:
            clave = (hashlib.sha1(img.read_raw_bytes()).hexdigest() + str(int(img.Width)) + "x"
                     + str(int(img.Height)) + str(img.get("/ColorSpace")) + str(img.get("/Filter"))
                     + str(img.get("/SMask", "")))
        except Exception:
            clave = None
        if clave and clave in huellas and huellas[clave].objgen != og:
            xobjs[nombre] = huellas[clave]
            hechas.add(og)
            return
        if calidad is not None:
            _recomprimir_imagen(img, calidad)
        hechas.add(og)
        if clave:
            huellas[clave] = img

    for i, page in enumerate(pdf.pages):
        if cancelar is not None and cancelar.is_set():
            raise Cancelado()
        if i % 20 == 0:
            estado(f"Comprimiendo imágenes... página {i + 1} de {total}")
        po = page.obj
        for k in ("/PieceInfo", "/Thumb"):
            if k in po:
                del po[k]
        if i in omitir:
            continue
        _recorrer_xobjects(po.get("/Resources"), visitar, vistos_form)
    if "/PieceInfo" in pdf.Root:
        del pdf.Root["/PieceInfo"]


# =========================================================================
#  PROCESO COMPLETO
# =========================================================================
def nombre_salida(ruta):
    base, _ = os.path.splitext(ruta)
    salida = base + "_PdFOL.pdf"
    k = 2
    while os.path.exists(salida):
        salida = f"{base}_PdFOL ({k}).pdf"
        k += 1
    return salida


def procesar(ruta, pesadas=(), dpi=DPI_DEFECTO, nucleos=None, texto=True,
             folio=None, compresion=None, progreso=None, estado=None, cancelar=None, scores=None,
             ya_listas=(), marcar_listas=False):
    """pesadas: paginas a aplanar (vacio = no aplanar).
    folio: dict de foliado o None.  compresion: None o 'sin-perdida'/'equilibrada'/'alta'."""
    cancelar = cancelar or threading.Event()
    progreso = progreso or (lambda h, t, eta: None)
    estado = estado or (lambda msg: None)
    ya_listas = set(ya_listas)
    pesadas = sorted(set(pesadas) - ya_listas)
    aplanar = bool(pesadas)
    if not aplanar and folio is None and compresion is None:
        raise ValueError("No hay nada que hacer: elegí aplanar, foliar o comprimir.")
    calidad = CALIDAD_MOSAICO.get(compresion, CALIDAD_JPEG)
    salida = nombre_salida(ruta)
    carpeta_tmp = os.path.splitext(salida)[0] + "_temporal"
    t0 = time.time()
    pool = manager = None
    tmp_abiertos, resultados = [], []
    nucleos_usados = foliadas = 0
    try:
        # ---- 1. aplanar (en paralelo)
        if aplanar:
            os.makedirs(carpeta_tmp, exist_ok=True)
            nucleos = nucleos or nucleos_recomendados(dpi)
            nucleos_usados = nucleos = max(1, min(nucleos, len(pesadas)))
            tam = max(1, min(8, math.ceil(len(pesadas) / (nucleos * 3))))
            bloques = [pesadas[k:k + tam] for k in range(0, len(pesadas), tam)]
            manager = mp.Manager()
            cola = manager.Queue()
            pool = mp.Pool(nucleos, initializer=_iniciar_trabajador, initargs=(ruta, cola))
            estado(f"Aplanando {len(pesadas)} planos a {dpi} dpi con {nucleos} núcleos...")
            tareas = [pool.apply_async(_trabajar, (b, pags, dpi, calidad, texto, carpeta_tmp))
                      for b, pags in enumerate(bloques)]
            hechas = 0
            while True:
                if cancelar.is_set():
                    pool.terminate()
                    raise Cancelado()
                try:
                    cola.get(timeout=0.25)
                    hechas += 1
                    trans = time.time() - t0
                    progreso(hechas, len(pesadas), trans / hechas * (len(pesadas) - hechas))
                except queue.Empty:
                    pass
                for t in tareas:
                    if t.ready() and not t.successful():
                        t.get()
                if hechas >= len(pesadas) and all(t.ready() for t in tareas):
                    break
            resultados = [t.get() for t in tareas]
            pool.close()
            pool.join()

        estado("Armando el PDF final...")
        pdf = pikepdf.open(ruta)

        # ---- compresion de imagenes de paginas NO aplanadas (antes de foliar)
        if compresion is not None:
            comprimir_pdf(pdf, compresion, omitir=set(pesadas) | ya_listas, estado=estado, cancelar=cancelar)

        # ---- colocar planos aplanados
        for _, pags, ruta_tmp in sorted(resultados):
            tmp = pikepdf.open(ruta_tmp)
            tmp_abiertos.append(tmp)
            for k, i in enumerate(pags):
                _reemplazar_pagina(pdf, pdf.pages[i], tmp, tmp.pages[k])
            if cancelar.is_set():
                raise Cancelado()

        # ---- 2. foliar
        if folio is not None:
            foliadas = aplicar_folios(pdf, folio, estado=estado, cancelar=cancelar)

        # ---- 3. comprimir estructura y guardar
        if cancelar.is_set():
            raise Cancelado()
        listas = set(ya_listas)
        if marcar_listas and compresion is not None:
            listas = set(range(len(pdf.pages)))
        if listas:
            pdf.Root[Name("/" + CLAVE_LISTAS)] = pikepdf.String(texto_rangos(listas))
        if compresion is not None:
            estado("Comprimiendo y guardando (con archivos grandes puede tardar varios minutos)...")
            pikepdf.settings.set_flate_compression_level(9)
            pdf.save(salida, object_stream_mode=pikepdf.ObjectStreamMode.generate,
                     stream_decode_level=pikepdf.StreamDecodeLevel.generalized,
                     recompress_flate=True, compress_streams=True)
        else:
            estado("Guardando (con archivos grandes puede tardar unos minutos)...")
            pdf.save(salida, object_stream_mode=pikepdf.ObjectStreamMode.generate,
                     stream_decode_level=pikepdf.StreamDecodeLevel.none, compress_streams=True)
        pdf.close()

        if scores is not None and aplanar:
            rep = os.path.splitext(salida)[0] + "_reporte.csv"
            conj = set(pesadas)
            with open(rep, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.writer(f)
                w.writerow(["pagina", "vectores_KB", "accion"])
                for i, s in enumerate(scores):
                    w.writerow([i + 1, round(s, 1), "APLANADA" if i in conj else "intacta"])

        return {"salida": salida, "planos": len(pesadas), "nucleos": nucleos_usados,
                "foliadas": foliadas, "compresion": compresion, "segundos": time.time() - t0,
                "mb_entrada": os.path.getsize(ruta) / 1048576,
                "mb_salida": os.path.getsize(salida) / 1048576}
    except BaseException:
        try:
            if pool is not None:
                pool.terminate()
        except Exception:
            pass
        if os.path.exists(salida):
            try:
                os.remove(salida)
            except Exception:
                pass
        raise
    finally:
        for t in tmp_abiertos:
            try:
                t.close()
            except Exception:
                pass
        try:
            if manager is not None:
                manager.shutdown()
        except Exception:
            pass
        shutil.rmtree(carpeta_tmp, ignore_errors=True)


# ---- paginas ya aplanadas y comprimidas: se marcan en el PDF para no repetir el proceso
CLAVE_LISTAS = "PdFOLListas"


def texto_rangos(indices):
    """{0,1,2,5} -> '1-3,6'"""
    xs = sorted(set(indices))
    partes, k = [], 0
    while k < len(xs):
        j = k
        while j + 1 < len(xs) and xs[j + 1] == xs[j] + 1:
            j += 1
        partes.append(str(xs[k] + 1) if j == k else f"{xs[k] + 1}-{xs[j] + 1}")
        k = j + 1
    return ",".join(partes)


def leer_listas(ruta):
    """Paginas (base 0) que PdFOL ya aplano y comprimio en este PDF."""
    try:
        d = fitz.open(ruta)
        try:
            tipo, val = d.xref_get_key(d.pdf_catalog(), CLAVE_LISTAS)
            n = d.page_count
        finally:
            d.close()
        if tipo != "string" or not val:
            return set()
        return parsear_paginas(val, n)
    except Exception:
        return set()


# ---- organizar: trabajo pesado en un PROCESO aparte (la ventana nunca se congela)
def armar_organizado(orden, fuentes, destino, avance=None, cancelar=None):
    """orden: [(fuente, pagina, giro)] -> PDF nuevo en 'destino' con las paginas listas marcadas."""
    docs = {}
    out = fitz.open()
    k = 0
    n = len(orden)
    while k < n:
        if cancelar is not None and cancelar.is_set():
            raise Cancelado()
        fid, pag, rot = orden[k]
        j = k
        while j + 1 < n and j - k < 49 and orden[j + 1] == (fid, pag + (j + 1 - k), rot):
            j += 1
        if fid not in docs:
            docs[fid] = fitz.open(fuentes[fid])
        ini = len(out)
        out.insert_pdf(docs[fid], from_page=pag, to_page=pag + (j - k))
        if rot:
            for q in range(ini, len(out)):
                out[q].set_rotation((out[q].rotation + rot) % 360)
        k = j + 1
        if avance:
            avance(k, n)
    listas_f = {fid: leer_listas(fuentes[fid]) for fid in {f_ for f_, _p, _r in orden}}
    listas = [q for q, (fid, pag, _r) in enumerate(orden) if pag in listas_f[fid]]
    if listas:
        out.xref_set_key(out.pdf_catalog(), CLAVE_LISTAS, f"({texto_rangos(listas)})")
    tmp = destino + ".tmp"
    out.save(tmp, garbage=1, deflate=True)
    out.close()
    for d in docs.values():
        d.close()
    os.replace(tmp, destino)


def _proceso_organizar(tarea, p, cola, cancelar):
    """Corre en otro proceso. Avisa por 'cola' con los mismos mensajes que usa la interfaz."""
    fitz.TOOLS.mupdf_display_errors(False)
    try:
        if tarea == "preparar":
            listos = []
            rutas = p["rutas"]
            for k, r_ in enumerate(rutas, 1):
                nom = os.path.basename(r_)
                cab = f"PDF {k} de {len(rutas)} · {nom}: " if len(rutas) > 1 else f"{nom}: "
                sub = os.path.join(p["tmp"], f"p{os.getpid()}_{k}_{int(time.time())}")
                os.makedirs(sub, exist_ok=True)
                copia = os.path.join(sub, nom)
                cola.put((("prep_estado",), cab + "copiando…"))
                shutil.copy2(r_, copia)
                cola.put((("prep_estado",), cab + "buscando planos pesados…"))
                scores, umbral = analizar(copia, lambda h, t_: cola.put((("prep_prog",), (h, t_))), cancelar)
                pes = {i for i, s_ in enumerate(scores) if s_ >= umbral}
                r = procesar(copia, pes, dpi=p["dpi"], texto=p["texto"], compresion=p["nivel"], marcar_listas=True,
                             progreso=lambda h, t_, eta: cola.put((("prep_prog",), (h, t_))),
                             estado=lambda m: cola.put((("prep_estado",), cab + m)), cancelar=cancelar)
                try:
                    os.remove(copia)
                except Exception:
                    pass
                listos.append((r_, r["salida"], len(pes), r["mb_entrada"], r["mb_salida"]))
            cola.put((("prep_listo",), listos))
            return
        # ---- final: armar + aplanar lo que falte + comprimir + foliar
        tramos = {"armar": (0.0, 0.10), "buscar": (0.10, 0.15), "procesar": (0.25, 0.75)}

        def fase(nombre, h, t_):
            a_, w_ = tramos[nombre]
            cola.put((("fase",), (a_ + w_ * h / max(1, t_), h, t_)))

        carpeta = os.path.join(p["tmp"], f"final_{os.getpid()}_{int(time.time())}")
        os.makedirs(carpeta, exist_ok=True)
        try:
            dest = p["dest"]
            armado = os.path.join(carpeta, os.path.basename(dest))
            armar_organizado(p["orden"], p["fuentes"], armado, avance=lambda h, t_: fase("armar", h, t_),
                             cancelar=cancelar)
            ya = leer_listas(armado)
            pes = set()
            if p["apl"] and len(ya) < len(p["orden"]):
                cola.put((("prep_estado",), "Paso 2 de 3 · Buscando planos pesados que falten…"))
                sc, um = analizar(armado, lambda h, t_: fase("buscar", h, t_), cancelar)
                pes = {i for i, s_ in enumerate(sc) if s_ >= um} - ya
            if not pes and p["compresion"] is None and p["folio"] is None:
                shutil.copy2(armado, dest)
                r = {"planos": 0}
            else:
                cola.put((("prep_estado",), "Paso 3 de 3 · Procesando…"))
                r = procesar(armado, pes, dpi=p["dpi"], nucleos=p["nucleos"], texto=p["texto"], folio=p["folio"],
                             compresion=p["compresion"], progreso=lambda h, t_, eta: fase("procesar", h, t_),
                             estado=lambda m: cola.put((("prep_estado",), "Paso 3 de 3 · " + m)),
                             cancelar=cancelar, ya_listas=ya, marcar_listas=p["apl"] and p["compresion"] is not None)
                if os.path.exists(dest):
                    os.remove(dest)
                shutil.move(r["salida"], dest)
            cola.put((("final",), (dest, r.get("planos", 0), r.get("foliadas", 0), len(ya))))
        finally:
            shutil.rmtree(carpeta, ignore_errors=True)
    except Cancelado:
        cola.put((("prep_error",), None) if tarea == "preparar" else (("cancelado_final",), None))
    except BaseException as e:
        cola.put((("prep_error",), str(e)) if tarea == "preparar" else (("error",), str(e)))


# =========================================================================
#  VISOR: las paginas se dibujan en PROCESOS aparte (la ventana nunca se congela)
# =========================================================================
MAX_PIXELES_VISOR = 6_000_000   # mas grande que esto se dibuja por mosaicos
MOSAICO_VISOR = 1024


def matriz_vista(ancho, alto, z, rot=0, parar=False):
    """Matriz pagina -> pantalla (origen arriba a la izquierda) con zoom z, giro extra 'rot'
    (organizar) y 'parar' (horizontales paradas, encabezado hacia la perforacion)."""
    R = fitz.Rect(0, 0, ancho, alto)
    M = fitz.Matrix(z, z).prerotate(rot)
    b = R * M
    if parar and b.width > b.height * 1.001:
        M = M * fitz.Matrix(-90)
        b = R * M
    return M * fitz.Matrix(1, 0, 0, 1, -b.x0, -b.y0)


def dibujar_trozo(page, dl, z, rot=0, parar=False, folio=None, trozo=None):
    """Imagen RGB de la pagina (o de un trozo en coordenadas de pantalla) con el folio encima."""
    R = page.rect
    M = matriz_vista(R.width, R.height, z, rot, parar)
    total = fitz.Rect(0, 0, R.width, R.height) * M
    T = fitz.Rect(trozo) if trozo else total
    T = T & total
    clip = T * ~M
    pix = dl.get_pixmap(matrix=M, alpha=False, clip=clip)
    if pix.n != 3:
        pix = fitz.Pixmap(fitz.csRGB, pix)
    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
    if folio:
        # el folio se pone sobre la pagina ya girada (como queda al procesar)
        wr, hr = (R.height, R.width) if rot % 180 else (R.width, R.height)
        Mc = matriz_vista(wr, hr, z, 0, parar)
        capa = fitz.open()
        cp_ = capa.new_page(width=wr, height=hr)
        estampar_folio(cp_, folio[1], folio[0])
        px_ = cp_.get_pixmap(matrix=Mc, alpha=True, clip=T * ~Mc)
        ov = Image.frombytes("RGBA", (px_.width, px_.height), px_.samples)
        capa.close()
        if ov.size != img.size:
            ov = ov.resize(img.size)
        b_ = img.convert("RGBA")
        b_.alpha_composite(ov)
        img = b_.convert("RGB")
    return img


def dibujar_pagina(doc, pag, ancho_px, rot=0, parar=False, folio=None, alto_px=None):
    """Pagina entera que entre en ancho_px (x alto_px). La usa tambien Imprimir."""
    pg = doc[pag]
    R = pg.rect
    vw, vh = (fitz.Rect(0, 0, R.width, R.height) * matriz_vista(R.width, R.height, 1, rot, parar))[2:]
    z = ancho_px / max(vw, 1)
    if alto_px:
        z = min(z, alto_px / max(vh, 1))
    if vw * vh * z * z > 40_000_000:
        z = math.sqrt(40_000_000 / (vw * vh))
    return dibujar_trozo(pg, pg.get_displaylist(annots=True), z, rot, parar, folio)


def _abrir_cache(docs, orden, ruta, maximo=8):
    d = docs.get(ruta)
    if d is None:
        d = docs[ruta] = fitz.open(ruta)
    if ruta in orden:
        orden.remove(ruta)
    orden.append(ruta)
    while len(orden) > maximo:
        viejo = orden.pop(0)
        try:
            docs.pop(viejo).close()
        except Exception:
            pass
    return d


def _carpeta_tessdata():
    """Idiomas para reconocer texto (OCR): los que vienen con PdFOL; si no, los de Tesseract instalado."""
    for c_ in (os.path.join(carpeta_recursos(), "tessdata"), os.environ.get("TESSDATA_PREFIX") or ""):
        if c_ and os.path.isfile(os.path.join(c_, "spa.traineddata")):
            return c_
    try:
        return fitz.get_tessdata()
    except Exception:
        return None


def _colores_renglon(img, r_):
    """(tinta, papel) de un renglon de la hoja escaneada: lo mas oscuro y lo mas claro de la zona."""
    try:
        caja = img.crop((max(0, int(r_.x0)), max(0, int(r_.y0)), min(img.width, int(r_.x1) + 1),
                         min(img.height, int(r_.y1) + 1)))
        px_ = list(caja.getdata())
        if not px_:
            return (0, 0, 0), (255, 255, 255)
        px_.sort(key=lambda c: c[0] * 299 + c[1] * 587 + c[2] * 114)
        n_ = len(px_)
        osc = px_[: max(1, n_ // 12)]
        cla = px_[int(n_ * 0.55): max(int(n_ * 0.55) + 1, int(n_ * 0.9))]
        prom = lambda l_: tuple(int(sum(c[k] for c in l_) / len(l_)) for k in range(3))
        return prom(osc), prom(cla)
    except Exception:
        return (0, 0, 0), (255, 255, 255)


def _unir_parrafos(bloques):
    """El OCR da un bloque por renglon: se juntan los renglones seguidos del mismo parrafo (mismo margen
    izquierdo, letra parecida y poca separacion), como en un PDF de texto."""
    lineas = sorted((ln for bl in bloques for ln in bl["lines"]), key=lambda l_: (l_["bbox"][1], l_["bbox"][0]))
    out = []
    for ln in lineas:
        x0, y0, x1, y1 = ln["bbox"]
        h_ = max(1.0, y1 - y0)
        if out:
            ult = out[-1]["lines"][-1]["bbox"]
            hu = max(1.0, ult[3] - ult[1])
            if (abs(x0 - out[-1]["bbox"][0]) < 1.5 * h_ and 0 <= y0 - ult[3] < 0.95 * max(h_, hu)
                    and abs(h_ - hu) < 0.45 * max(h_, hu)):
                b_ = out[-1]
                b_["lines"].append(ln)
                b_["bbox"] = (min(b_["bbox"][0], x0), b_["bbox"][1], max(b_["bbox"][2], x1), y1)
                continue
        out.append({"bbox": tuple(ln["bbox"]), "lines": [ln]})
    return out


def _proceso_ocr(entrada, salida):
    """v4.1: reconoce el texto de paginas escaneadas (Tesseract dentro de MuPDF), fuera de la ventana.
    Recibe (ruta, pag, ver); responde (ruta, pag, ver, letras, bloques) o (ruta, pag, ver, None, error)."""
    if sys.stdout is None:
        sys.stdout = open(os.devnull, "w")
    if sys.stderr is None:
        sys.stderr = open(os.devnull, "w")
    fitz.TOOLS.mupdf_display_errors(False)
    tess = _carpeta_tessdata()
    while True:
        msg = entrada.get()
        if msg is None:
            return
        ruta, pag, ver_ = msg
        try:
            if not tess:
                raise RuntimeError("faltan los idiomas del OCR (carpeta tessdata)")
            with fitz.open(ruta) as d_:
                pg = d_[pag]
                idiomas = "+".join(l_ for l_ in ("spa", "eng") if os.path.isfile(os.path.join(tess, l_ + ".traineddata")))
                tp = pg.get_textpage_ocr(language=idiomas or "eng", dpi=300, full=True, tessdata=tess)
                m = pg.rotation_matrix
                letras, lid = [], 0
                for bl in pg.get_text("rawdict", textpage=tp)["blocks"]:
                    for ln in bl.get("lines", []):
                        lid += 1
                        for sp in ln["spans"]:
                            for ch in sp["chars"]:
                                r_ = fitz.Rect(ch["bbox"]) * m
                                letras.append((r_.x0, r_.y0, r_.x1, r_.y1, lid, ch["c"]))
                esc = 2.0
                pix = pg.get_pixmap(matrix=fitz.Matrix(esc, esc), alpha=False)
                img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                bloques = []
                for bl in pg.get_text("dict", textpage=tp)["blocks"]:
                    if bl.get("type", 0) != 0:
                        continue
                    lineas = []
                    for ln in bl.get("lines", []):
                        spans = [{k_: sp[k_] for k_ in ("text", "size", "font", "flags", "color", "origin", "bbox")}
                                 for sp in ln["spans"]]
                        rv = fitz.Rect(ln["bbox"]) * m
                        tinta, papel = _colores_renglon(img, rv * esc)
                        lineas.append({"bbox": ln["bbox"], "dir": ln["dir"], "spans": spans, "tinta": tinta,
                                       "papel": papel})
                    bloques.append({"bbox": bl["bbox"], "lines": lineas})
                bloques = _unir_parrafos(bloques)
            salida.put((ruta, pag, ver_, letras, bloques))
        except Exception as e:
            salida.put((ruta, pag, ver_, None, str(e)))


def _proceso_miniaturas_org(entrada, salida):
    """v4.0: miniaturas de Organizar en un proceso aparte (antes un hilo: competia con la ventana y la trababa).
    Recibe (clave, ruta, pag, ancho), ("gen", n) para descartar lo viejo, ("cerrar", ruta) o None.
    Responde (clave, ancho, alto, bytes RGB) o (clave, None)."""
    if sys.stdout is None:
        sys.stdout = open(os.devnull, "w")
    if sys.stderr is None:
        sys.stderr = open(os.devnull, "w")
    fitz.TOOLS.mupdf_display_errors(False)
    abiertos, orden_ = {}, []
    gen = None
    while True:
        msg = entrada.get()
        if msg is None:
            return
        if msg[0] == "gen":
            gen = msg[1]
            continue
        if msg[0] == "cerrar":
            d = abiertos.pop(msg[1], None)
            if d is not None:
                orden_.remove(msg[1])
                d.close()
            continue
        clave, ruta_f, pag, ancho = msg
        if gen is not None and clave[0] != gen:
            continue
        try:
            d = abiertos.get(ruta_f)
            if d is None:
                d = abiertos[ruta_f] = fitz.open(ruta_f)
                orden_.append(ruta_f)
                while len(orden_) > 8:
                    abiertos.pop(orden_.pop(0)).close()
            pg = d[pag]
            z = ancho / max(pg.rect.width, pg.rect.height)
            pix = pg.get_pixmap(matrix=fitz.Matrix(z, z), alpha=False)
            salida.put((clave, pix.width, pix.height, pix.samples))
        except Exception:
            salida.put((clave, None))


def _proceso_render(entrada, salida):
    """Proceso que dibuja paginas. Recibe por 'entrada':
         ("ver", [(clave, ruta, pag, z, rot, parar, folio, trozo), ...])  -> reemplaza lo pendiente
         ("medidas", ruta)  -> tamanos de todas las paginas
         ("cerrar", ruta)   -> soltar el archivo (por ejemplo, para guardar resaltados)
         None               -> terminar
       Responde por 'salida' (clave, ancho, alto, bytes RGB) o ("medidas", ruta, [(w, h)], error)."""
    if sys.stdout is None:
        sys.stdout = open(os.devnull, "w")
    if sys.stderr is None:
        sys.stderr = open(os.devnull, "w")
    fitz.TOOLS.mupdf_display_errors(False)
    salida.put(("listo",))  # v3.0: avisa que ya dibuja (hasta aca, la primera hoja la dibuja la ventana)
    docs, orden_docs = {}, []
    dls, orden_dls = {}, []
    recientes = {}  # clave -> hora de envio (no repetir lo que ya va en camino)
    pend = []

    def lista_de(ruta, pag):
        k_ = (ruta, pag)
        dl = dls.get(k_)
        if dl is None:
            dl = dls[k_] = _abrir_cache(docs, orden_docs, ruta)[pag].get_displaylist(annots=True)
        if k_ in orden_dls:
            orden_dls.remove(k_)
        orden_dls.append(k_)
        while len(orden_dls) > 6:
            dls.pop(orden_dls.pop(0), None)
        return dl

    def atender(msg):
        nonlocal pend
        if msg[0] == "ver":
            pend = list(msg[1])
        elif msg[0] == "medidas":
            ruta = msg[1]
            try:
                d = _abrir_cache(docs, orden_docs, ruta)
                med = [(d[i].rect.width, d[i].rect.height) for i in range(d.page_count)]
                salida.put(("medidas", ruta, med, None))
            except Exception as e:
                salida.put(("medidas", ruta, [], str(e)))
        elif msg[0] == "cerrar":
            for k_ in [k_ for k_ in dls if k_[0] == msg[1]]:
                dls.pop(k_, None)
                orden_dls.remove(k_)
            d = docs.pop(msg[1], None)
            if d is not None:
                orden_docs.remove(msg[1])
                d.close()
            for k_ in [k_ for k_ in recientes if len(k_) > 1 and k_[1] == msg[1]]:
                recientes.pop(k_, None)

    while True:
        try:
            msg = entrada.get(timeout=None if not pend else 0.001)
            if msg is None:
                return
            atender(msg)
            while True:
                msg = entrada.get_nowait()
                if msg is None:
                    return
                atender(msg)
        except queue.Empty:
            pass
        except (EOFError, OSError):
            return
        if not pend:
            continue
        clave, ruta, pag, z, rot, parar, folio, trozo = pend.pop(0)
        if time.time() - recientes.get(clave, 0) < 4:
            continue
        try:
            d = _abrir_cache(docs, orden_docs, ruta)
            img = dibujar_trozo(d[pag], lista_de(ruta, pag), z, rot, parar, folio, trozo)
            salida.put((clave, img.width, img.height, img.tobytes()))
        except Exception:
            salida.put((clave, 0, 0, None))
        recientes[clave] = time.time()
        if len(recientes) > 600:
            for k_ in sorted(recientes, key=recientes.get)[:300]:
                recientes.pop(k_, None)


def _rects_pagina(page, rects):
    """Rectangulos del texto (sin girar) -> coordenadas de la pagina tal como se ve."""
    m = page.rotation_matrix
    return [tuple(fitz.Rect(r) * m) for r in rects]


def _proceso_buscar(entrada, salida):
    """Busca texto y palabras en otro proceso. Recibe:
         ("buscar", id, texto, [(ruta, pag), ...])  -> ("hallazgos", id, [(pos, [rects])], fin, hechas, total)
         ("palabras", id, ruta, pag, rect)          -> ("palabras", id, ruta, pag, [rects por renglon])
    Los rectangulos van en coordenadas de la pagina como se ve (page.rect)."""
    if sys.stdout is None:
        sys.stdout = open(os.devnull, "w")
    if sys.stderr is None:
        sys.stderr = open(os.devnull, "w")
    fitz.TOOLS.mupdf_display_errors(False)
    docs, orden_docs = {}, []
    trabajo = None
    while True:
        try:
            msg = entrada.get(timeout=None if trabajo is None else 0.0005)
            if msg is None:
                return
            if msg[0] == "buscar":
                _, ident, texto, lista = msg
                trabajo = {"id": ident, "texto": texto, "lista": lista, "k": 0, "lote": []}
            elif msg[0] == "parar":
                trabajo = None
            elif msg[0] == "cerrar":
                d = docs.pop(msg[1], None)
                if d is not None:
                    orden_docs.remove(msg[1])
                    d.close()
            elif msg[0] == "caracteres":
                _, ruta, pag, ver_ = msg
                out = []
                try:
                    pg = _abrir_cache(docs, orden_docs, ruta)[pag]
                    m = pg.rotation_matrix
                    lid = 0
                    for bl in pg.get_text("rawdict")["blocks"]:
                        for ln in bl.get("lines", []):
                            lid += 1
                            for sp in ln["spans"]:
                                for ch in sp["chars"]:
                                    r_ = fitz.Rect(ch["bbox"]) * m
                                    out.append((r_.x0, r_.y0, r_.x1, r_.y1, lid, ch["c"]))
                except Exception:
                    pass
                salida.put(("caracteres", ruta, pag, ver_, out))
            elif msg[0] == "palabras":
                _, ident, ruta, pag, rect = msg
                try:
                    pg = _abrir_cache(docs, orden_docs, ruta)[pag]
                    clip = fitz.Rect(rect) * pg.derotation_matrix
                    lineas = {}
                    for x0, y0, x1, y1, _w, b_, l_, _n in pg.get_text("words", clip=clip):
                        r_ = fitz.Rect(x0, y0, x1, y1)
                        if not r_.intersects(clip):
                            continue
                        lineas[(b_, l_)] = lineas[(b_, l_)] | r_ if (b_, l_) in lineas else r_
                    salida.put(("palabras", ident, ruta, pag, _rects_pagina(pg, lineas.values())))
                except Exception:
                    salida.put(("palabras", ident, ruta, pag, []))
            continue
        except queue.Empty:
            pass
        except (EOFError, OSError):
            return
        if trabajo is None:
            continue
        t = trabajo
        if t["k"] < len(t["lista"]):
            ruta, pag = t["lista"][t["k"]]
            try:
                pg = _abrir_cache(docs, orden_docs, ruta)[pag]
                rs = pg.search_for(t["texto"])
                if rs:
                    t["lote"].append((t["k"], _rects_pagina(pg, rs)))
            except Exception:
                pass
            t["k"] += 1
        fin = t["k"] >= len(t["lista"])
        if fin or len(t["lote"]) >= 20 or (t["k"] % 40 == 0):
            salida.put(("hallazgos", t["id"], t["lote"], fin, t["k"], len(t["lista"])))
            t["lote"] = []
        if fin:
            trabajo = None


# =========================================================================
#  IMPRIMIR (Windows: directo a la impresora con GDI, en un proceso aparte)
# =========================================================================
PAPELES = {"Carta": (612.0, 792.0, 1), "Oficio": (612.0, 1008.0, 5), "A3": (841.9, 1190.6, 8)}
DPI_IMPRESION = 300


def papel_de_pagina(w, h, forzado="Automático"):
    """Papel en que sale la pagina: automatico (carta, o A3 los planos) o el elegido."""
    if forzado in PAPELES:
        return forzado
    return papel_fisico(w, h)[0]


def colocar_en_hoja(img_w, img_h, dpi_img, area_w, area_h, dpi_dev, ajustar):
    """Donde va la imagen en la hoja (pixeles del dispositivo): (x, y, ancho, alto), centrada."""
    if ajustar:
        f = min(area_w / max(img_w, 1), area_h / max(img_h, 1))
    else:  # tamano real
        f = dpi_dev / max(dpi_img, 1)
    w, h = int(round(img_w * f)), int(round(img_h * f))
    return (area_w - w) // 2, (area_h - h) // 2, w, h


def impresoras_windows():
    """(nombres, predeterminada) de las impresoras instaladas."""
    if os.name != "nt":
        return [], None
    import ctypes
    from ctypes import wintypes
    ws = ctypes.WinDLL("winspool.drv")

    class PI4(ctypes.Structure):
        _fields_ = [("pPrinterName", wintypes.LPWSTR), ("pServerName", wintypes.LPWSTR),
                    ("Attributes", wintypes.DWORD)]
    nombres = []
    try:
        necesita, cuantos = wintypes.DWORD(0), wintypes.DWORD(0)
        ws.EnumPrintersW(6, None, 4, None, 0, ctypes.byref(necesita), ctypes.byref(cuantos))
        buf = ctypes.create_string_buffer(max(1, necesita.value))
        if ws.EnumPrintersW(6, None, 4, buf, necesita, ctypes.byref(necesita), ctypes.byref(cuantos)):
            arr = ctypes.cast(buf, ctypes.POINTER(PI4))
            nombres = [arr[i].pPrinterName for i in range(cuantos.value)]
    except Exception:
        pass
    pred = None
    try:
        n = wintypes.DWORD(0)
        ws.GetDefaultPrinterW(None, ctypes.byref(n))
        b = ctypes.create_unicode_buffer(max(1, n.value))
        if ws.GetDefaultPrinterW(b, ctypes.byref(n)):
            pred = b.value
    except Exception:
        pass
    return nombres, pred


def _devmode(nombre, base=None, hwnd=None, preguntar=False):
    """DEVMODE de la impresora (bytes). Con 'preguntar' abre la ventana de propiedades de la impresora."""
    import ctypes
    from ctypes import wintypes
    ws = ctypes.WinDLL("winspool.drv")
    h = wintypes.HANDLE()
    if not ws.OpenPrinterW(nombre, ctypes.byref(h), None):
        raise OSError("No se pudo abrir la impresora.")
    try:
        tam = ws.DocumentPropertiesW(hwnd, h, nombre, None, None, 0)
        if tam <= 0:
            raise OSError("La impresora no respondió.")
        sal = ctypes.create_string_buffer(tam)
        ent = None
        modo = 2  # DM_OUT_BUFFER
        if base and len(base) <= tam:
            ent = ctypes.create_string_buffer(base, tam)
            modo |= 8  # DM_IN_BUFFER
        if preguntar:
            modo |= 4  # DM_IN_PROMPT
        r = ws.DocumentPropertiesW(hwnd, h, nombre, sal, ent, modo)
        if preguntar and r != 1:  # Cancelar
            return base
        return sal.raw
    finally:
        ws.ClosePrinter(h)


def _proceso_imprimir(p, cola, cancelar):
    """Imprime en otro proceso. p: impresora, devmode, paginas [(ruta, pag, rot, folio)], copias,
    intercalar, papel, ajustar, titulo. Avisa por 'cola'."""
    if sys.stdout is None:
        sys.stdout = open(os.devnull, "w")
    if sys.stderr is None:
        sys.stderr = open(os.devnull, "w")
    fitz.TOOLS.mupdf_display_errors(False)
    try:
        orden = []
        if p["intercalar"]:
            for _c in range(p["copias"]):
                orden += list(range(len(p["paginas"])))
        else:
            for k in range(len(p["paginas"])):
                orden += [k] * p["copias"]
        docs = {}

        def imagen(k, dpi):
            ruta, pag, rot, folio = p["paginas"][k]
            d = docs.get(ruta) or docs.setdefault(ruta, fitz.open(ruta))
            pg = d[pag]
            w0, h0 = pg.rect.width, pg.rect.height
            if rot % 180:
                w0, h0 = h0, w0
            papel = papel_de_pagina(w0, h0, p["papel"])
            pw, ph, _cod = PAPELES[papel]
            vw, vh = (h0, w0) if w0 > h0 * 1.001 else (w0, h0)  # parada (encabezado a la perforacion)
            z = dpi / 72.0 if not p["ajustar"] else min(pw / vw, ph / vh) * dpi / 72.0
            z = min(z, math.sqrt(60_000_000 / max(1.0, w0 * h0)))
            img = dibujar_trozo(pg, pg.get_displaylist(annots=True), z, rot, True, folio)
            return img, papel, z * 72.0

        if os.name != "nt" or p.get("como_pdf"):
            # sin Windows (pruebas): arma un PDF con las hojas tal como saldrian impresas
            out = fitz.open()
            for n_, k in enumerate(orden, 1):
                if cancelar.is_set():
                    cola.put(("imp_cancelado", None))
                    return
                img, papel, dpi_img = imagen(k, 150)
                pw, ph, _ = PAPELES[papel]
                hoja = out.new_page(width=pw, height=ph)
                m = 12.0
                x, y, w, h = colocar_en_hoja(img.width, img.height, dpi_img, pw - 2 * m, ph - 2 * m, 72.0, p["ajustar"])
                b = io.BytesIO()
                img.save(b, "JPEG", quality=85)
                hoja.insert_image(fitz.Rect(m + x, m + y, m + x + w, m + y + h), stream=b.getvalue())
                cola.put(("imp_prog", (n_, len(orden))))
            out.save(p["como_pdf"] or os.path.join(os.path.expanduser("~"), "PdFOL_impresion.pdf"))
            cola.put(("imp_fin", len(orden)))
            return

        import ctypes
        from ctypes import wintypes
        gdi = ctypes.WinDLL("gdi32")
        gdi.CreateDCW.restype = wintypes.HDC
        gdi.CreateDCW.argtypes = [wintypes.LPCWSTR, wintypes.LPCWSTR, wintypes.LPCWSTR, ctypes.c_void_p]
        gdi.ResetDCW.restype = wintypes.HDC
        gdi.ResetDCW.argtypes = [wintypes.HDC, ctypes.c_void_p]
        gdi.StretchDIBits.argtypes = [wintypes.HDC] + [ctypes.c_int] * 8 + [ctypes.c_char_p, ctypes.c_void_p,
                                                                             wintypes.UINT, wintypes.DWORD]
        gdi.GetDeviceCaps.argtypes = [wintypes.HDC, ctypes.c_int]

        class DOCINFOW(ctypes.Structure):
            _fields_ = [("cbSize", ctypes.c_int), ("lpszDocName", wintypes.LPCWSTR), ("lpszOutput", wintypes.LPCWSTR),
                        ("lpszDatatype", wintypes.LPCWSTR), ("fwType", wintypes.DWORD)]

        class BIH(ctypes.Structure):
            _fields_ = [("biSize", wintypes.DWORD), ("biWidth", ctypes.c_long), ("biHeight", ctypes.c_long),
                        ("biPlanes", wintypes.WORD), ("biBitCount", wintypes.WORD), ("biCompression", wintypes.DWORD),
                        ("biSizeImage", wintypes.DWORD), ("biXPelsPerMeter", ctypes.c_long),
                        ("biYPelsPerMeter", ctypes.c_long), ("biClrUsed", wintypes.DWORD),
                        ("biClrImportant", wintypes.DWORD)]

        dm = bytearray(p["devmode"] or _devmode(p["impresora"]))
        dmb = ctypes.create_string_buffer(bytes(dm), len(dm))

        def ajustar_devmode(papel):
            campos = int.from_bytes(dm[72:76], "little") | 0x1 | 0x2  # DM_ORIENTATION | DM_PAPERSIZE
            dm[72:76] = campos.to_bytes(4, "little")
            dm[76:78] = (1).to_bytes(2, "little")                      # vertical (las horizontales van paradas)
            dm[78:80] = PAPELES[papel][2].to_bytes(2, "little")
            ctypes.memmove(dmb, bytes(dm), len(dm))

        ajustar_devmode("Carta")
        hdc = gdi.CreateDCW("WINSPOOL", p["impresora"], None, dmb)
        if not hdc:
            raise OSError("No se pudo preparar la impresora.")
        di = DOCINFOW(ctypes.sizeof(DOCINFOW), p["titulo"], None, None, 0)
        if gdi.StartDocW(hdc, ctypes.byref(di)) <= 0:
            gdi.DeleteDC(hdc)
            raise OSError("La impresora no aceptó el trabajo.")
        try:
            for n_, k in enumerate(orden, 1):
                if cancelar.is_set():
                    gdi.AbortDoc(hdc)
                    cola.put(("imp_cancelado", None))
                    return
                dpi_dev = gdi.GetDeviceCaps(hdc, 88) or 300
                img, papel, dpi_img = imagen(k, min(DPI_IMPRESION, dpi_dev))
                ajustar_devmode(papel)
                gdi.ResetDCW(hdc, dmb)
                gdi.StartPage(hdc)
                area_w, area_h = gdi.GetDeviceCaps(hdc, 8), gdi.GetDeviceCaps(hdc, 10)  # HORZRES, VERTRES
                dpi_dev = gdi.GetDeviceCaps(hdc, 88) or 300
                x, y, w, h = colocar_en_hoja(img.width, img.height, dpi_img, area_w, area_h, dpi_dev, p["ajustar"])
                if img.width % 4:
                    lienzo = Image.new("RGB", (img.width + (-img.width % 4), img.height), "white")
                    lienzo.paste(img, (0, 0))
                    iw = img.width
                    img = lienzo
                else:
                    iw = img.width
                bits = img.tobytes("raw", "BGR")
                bih = BIH(ctypes.sizeof(BIH), img.width, -img.height, 1, 24, 0, 0, 0, 0, 0, 0)
                gdi.StretchDIBits(hdc, x, y, w, h, 0, 0, iw, img.height, bits, ctypes.byref(bih), 0, 0x00CC0020)
                gdi.EndPage(hdc)
                cola.put(("imp_prog", (n_, len(orden))))
            gdi.EndDoc(hdc)
        finally:
            gdi.DeleteDC(hdc)
        cola.put(("imp_fin", len(orden)))
    except BaseException as e:
        cola.put(("imp_error", str(e)))


# =========================================================================
#  ACTUALIZACIONES (releases del repositorio publico de GitHub)
# =========================================================================
REPO_GITHUB = "realmenes-gif/PdFOL"
ZIP_PORTABLE = "PdFOL_portable.zip"
EXE_PORTABLE = "PdFOL.exe"
PUERTO_INSTANCIA = 47391


def version_tupla(texto):
    import re
    nums = re.findall(r"\d+", str(texto or ""))
    return tuple(int(x) for x in nums[:4]) or (0,)


def ultima_version(timeout=6):
    """Datos del ultimo release publicado o None (sin internet, sin repositorio, etc.)."""
    import json as _json
    import urllib.request
    url = f"https://api.github.com/repos/{REPO_GITHUB}/releases/latest"
    req = urllib.request.Request(url, headers={"User-Agent": f"PdFOL/{VERSION_INTERNA}",
                                               "Accept": "application/vnd.github+json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        d = _json.loads(r.read().decode("utf-8"))
    zip_, sha = None, None
    for a in d.get("assets") or []:
        if a.get("name") == ZIP_PORTABLE:
            zip_ = a
        elif a.get("name") == ZIP_PORTABLE + ".sha256":
            sha = a
    return {"tag": d.get("tag_name", ""), "notas": d.get("body") or "", "web": d.get("html_url", ""),
            "zip": zip_, "sha": sha}


def hay_version_nueva(info):
    return bool(info and info.get("zip")) and version_tupla(info["tag"]) > version_tupla(VERSION_INTERNA)


def descargar_actualizacion(info, carpeta, progreso=None, cancelar=None):
    """Baja el zip, comprueba el SHA256 y lo descomprime. Devuelve la carpeta con PdFOL.exe."""
    import urllib.request
    import zipfile
    os.makedirs(carpeta, exist_ok=True)
    destino = os.path.join(carpeta, ZIP_PORTABLE)
    req = urllib.request.Request(info["zip"]["browser_download_url"], headers={"User-Agent": "PdFOL"})
    h = hashlib.sha256()
    with urllib.request.urlopen(req, timeout=30) as r, open(destino, "wb") as f:
        total = int(r.headers.get("Content-Length") or info["zip"].get("size") or 0)
        hecho = 0
        while True:
            if cancelar is not None and cancelar.is_set():
                raise Cancelado()
            b = r.read(1 << 20)
            if not b:
                break
            f.write(b)
            h.update(b)
            hecho += len(b)
            if progreso:
                progreso(hecho, total)
    esperado = None
    dig = (info["zip"].get("digest") or "")
    if dig.startswith("sha256:"):
        esperado = dig.split(":", 1)[1].strip().lower()
    elif info.get("sha"):
        req = urllib.request.Request(info["sha"]["browser_download_url"], headers={"User-Agent": "PdFOL"})
        with urllib.request.urlopen(req, timeout=20) as r:
            esperado = r.read().decode("ascii", "ignore").split()[0].strip().lower()
    if not esperado:
        raise ValueError("El release no trae la suma SHA256: no se instala por seguridad.")
    if h.hexdigest().lower() != esperado:
        raise ValueError("La descarga no coincide con su SHA256 (archivo dañado o alterado). No se instaló nada.")
    nuevo = os.path.join(carpeta, "nuevo")
    shutil.rmtree(nuevo, ignore_errors=True)
    with zipfile.ZipFile(destino) as z:
        z.extractall(nuevo)
    for raiz_, _dirs, archivos in os.walk(nuevo):
        if EXE_PORTABLE in archivos:
            return raiz_
    raise ValueError(f"El zip no trae {EXE_PORTABLE}.")


def lanzar_actualizador(nuevo, carpeta_tmp):
    """Escribe y arranca el pequeno actualizador: espera que PdFOL se cierre, reemplaza los archivos
    (conserva PdFOL_perfiles.json) y vuelve a abrir PdFOL."""
    import subprocess
    app_dir = os.path.dirname(sys.executable)
    pid = os.getpid()
    bat = os.path.join(carpeta_tmp, "actualizar_PdFOL.cmd")
    lineas = [
        "@echo off",
        "chcp 65001 >nul",
        "title Actualizando PdFOL",
        "set /a VUELTAS=0",
        ":esperar",
        f'tasklist /FI "PID eq {pid}" 2>nul | find "{pid}" >nul',
        "if errorlevel 1 goto listo_para_copiar",
        "set /a VUELTAS+=1",
        "if %VUELTAS% GEQ 20 goto forzar",
        "ping -n 2 127.0.0.1 >nul",
        "goto esperar",
        ":forzar",
        f"taskkill /F /T /PID {pid} >nul 2>nul",
        "ping -n 2 127.0.0.1 >nul",
        ":listo_para_copiar",
        'taskkill /F /IM PdFOL.exe >nul 2>nul',
        "ping -n 2 127.0.0.1 >nul",
        f'if exist "{app_dir}\\_internal" rmdir /s /q "{app_dir}\\_internal"',
        f'robocopy "{nuevo}" "{app_dir}" /E /XF PdFOL_perfiles.json /R:3 /W:1 /NFL /NDL /NJH /NJS /NP >nul',
        f'start "" "{os.path.join(app_dir, EXE_PORTABLE)}"',
        f'rmdir /s /q "{os.path.join(carpeta_tmp, "nuevo")}"',
        f'del /q "{os.path.join(carpeta_tmp, ZIP_PORTABLE)}"',
        '(goto) 2>nul & del "%~f0"',
    ]
    with open(bat, "w", encoding="utf-8", newline="\r\n") as f:
        f.write("\n".join(lineas) + "\n")
    si = subprocess.STARTUPINFO()
    si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
    si.wShowWindow = 0  # SW_HIDE
    subprocess.Popen(["cmd", "/c", bat], creationflags=0x08000000 | 0x00000200, startupinfo=si,
                     close_fds=True)  # CREATE_NO_WINDOW | CREATE_NEW_PROCESS_GROUP: no se ve ninguna ventana


def carpeta_escribible(carpeta):
    try:
        p = os.path.join(carpeta, ".pdfol_prueba_escritura")
        with open(p, "w") as f:
            f.write("ok")
        os.remove(p)
        return True
    except Exception:
        return False


def instancia_unica(rutas):
    """Si PdFOL ya esta abierto le pasa los PDF (se abren como pestanas) y devuelve None.
    Si no, devuelve un socket que escucha los de las proximas veces (o False si no se pudo).
    Todo con tiempo limite: un PdFOL colgado nunca deja esperando al nuevo."""
    import json as _json
    import socket
    clave = b"PdFOL-instancia-unica-1"
    try:
        c = socket.create_connection(("127.0.0.1", PUERTO_INSTANCIA), timeout=1.5)
        try:
            c.settimeout(2.0)
            c.sendall(clave + b"\n" + _json.dumps([os.path.abspath(r) for r in rutas]).encode("utf-8") + b"\n")
            if c.recv(8).startswith(b"ok"):
                return None  # el otro PdFOL los abrio
        finally:
            c.close()
    except Exception:
        pass
    try:
        srv = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        srv.bind(("127.0.0.1", PUERTO_INSTANCIA))
        srv.listen(5)
        return srv
    except Exception:
        return False


def recibir_instancia(srv):
    """Espera conexiones de otros PdFOL. Devuelve la lista de PDF de cada una (generador)."""
    import json as _json
    clave = b"PdFOL-instancia-unica-1"
    while True:
        try:
            c, _dir = srv.accept()
        except Exception:
            time.sleep(0.2)
            continue
        try:
            c.settimeout(2.0)
            datos = b""
            while datos.count(b"\n") < 2 and len(datos) < 1_000_000:
                b_ = c.recv(65536)
                if not b_:
                    break
                datos += b_
            cab, _sep, resto = datos.partition(b"\n")
            if cab == clave:
                rutas = _json.loads(resto.split(b"\n")[0].decode("utf-8") or "[]")
                c.sendall(b"ok")
                yield rutas
        except Exception:
            pass
        finally:
            try:
                c.close()
            except Exception:
                pass


# =========================================================================
#  VISTA PREVIA DEL FOLIO (hilo propio)
# =========================================================================
class Previsualizador(threading.Thread):
    """Genera la miniatura de la pagina con el folio y un acercamiento del folio."""

    def __init__(self, salida, tam_mini=(250, 330), tam_zoom=(250, 110)):
        super().__init__(daemon=True)
        self.pedidos = queue.Queue()
        self.salida = salida
        self.tam_mini, self.tam_zoom = tam_mini, tam_zoom
        self._ruta = self._idx = None
        self._doc = self._dl = None
        self._rect = fitz.Rect(0, 0, 595, 842)

    def pedir(self, ruta, idx, cfg, texto, girar=False):
        self.pedidos.put((ruta, idx, dict(cfg), texto, girar))

    def run(self):
        fitz.TOOLS.mupdf_display_errors(False)
        while True:
            pedido = self.pedidos.get()
            try:  # quedarse solo con el ultimo pedido
                while True:
                    pedido = self.pedidos.get_nowait()
            except queue.Empty:
                pass
            try:
                self.salida(("preview",) + self._generar(*pedido))
            except Exception as e:
                self.salida(("preview_error", str(e)))

    def _cargar(self, ruta, idx):
        if ruta == self._ruta and idx == self._idx:
            return
        self._dl = None
        if self._doc is not None and ruta != self._ruta:
            self._doc.close()
            self._doc = None
        self._ruta, self._idx = ruta, idx
        if ruta and os.path.isfile(ruta):
            if self._doc is None:
                self._doc = fitz.open(ruta)
            idx = max(0, min(idx, self._doc.page_count - 1))
            page = self._doc[idx]
            self._rect = page.rect
            self._dl = page.get_displaylist(annots=True)
        else:
            self._rect = fitz.Rect(0, 0, 595, 842)

    def _render(self, escala, clip=None):
        R = self._rect
        clip = clip or R
        if self._dl is not None:
            pix = self._dl.get_pixmap(matrix=fitz.Matrix(escala, escala), alpha=False, clip=clip)
            if pix.n != 3:
                pix = fitz.Pixmap(fitz.csRGB, pix)
            return Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
        w = max(1, int(round(clip.width * escala)))
        h = max(1, int(round(clip.height * escala)))
        return Image.new("RGB", (w, h), "white")

    def _generar(self, ruta, idx, cfg, texto, girar=False):
        self._cargar(ruta, idx)
        R = self._rect
        acostada = R.width > R.height * 1.001
        parar = girar and acostada  # mostrar la hoja impresa parada (arriba -> izquierda)
        # capa solo con el folio (fondo transparente)
        capa = fitz.open()
        cp = capa.new_page(width=R.width, height=R.height)
        caja = estampar_folio(cp, texto, cfg)

        def con_folio(base, escala, clip):
            pix = cp.get_pixmap(matrix=fitz.Matrix(escala, escala), alpha=True, clip=clip)
            ov = Image.frombytes("RGBA", (pix.width, pix.height), pix.samples)
            if ov.size != base.size:
                ov = ov.resize(base.size)
            b = base.convert("RGBA")
            b.alpha_composite(ov)
            return b.convert("RGB")

        # miniatura de la pagina completa
        tw, th = self.tam_mini
        if parar:
            tw, th = th, tw
        esc = min(tw / R.width, th / R.height)
        mini = con_folio(self._render(esc), esc, R)
        d = ImageDraw.Draw(mini)
        m = caja + (-6, -4, 6, 4)
        d.rectangle([m.x0 * esc - 2, m.y0 * esc - 2, m.x1 * esc + 2, m.y1 * esc + 2], outline=(220, 30, 30), width=2)
        d.rectangle([0, 0, mini.width - 1, mini.height - 1], outline=(150, 150, 150))
        # acercamiento alrededor del folio
        zw, zh = self.tam_zoom
        if parar:
            zw, zh = zh, zw
        ancho = max(caja.width + 80, 160)
        alto = ancho * zh / zw
        if alto < caja.height + 30:
            alto = caja.height + 30
            ancho = alto * zw / zh
        if parar:  # texto vertical en la pagina acostada
            alto = max(caja.height + 80, 160)
            ancho = alto * zw / zh
            if ancho < caja.width + 30:
                ancho = caja.width + 30
                alto = ancho * zh / zw
        cx, cy = (caja.x0 + caja.x1) / 2, (caja.y0 + caja.y1) / 2
        clip = fitz.Rect(cx - ancho / 2, cy - alto / 2, cx + ancho / 2, cy + alto / 2)
        # mantener la ventana dentro de la pagina
        dx = max(0, R.x0 - clip.x0) - max(0, clip.x1 - R.x1)
        dy = max(0, R.y0 - clip.y0) - max(0, clip.y1 - R.y1)
        clip = (clip + (dx, dy, dx, dy)) & R
        ez = min(zw / clip.width, zh / clip.height)
        zoom = con_folio(self._render(ez, clip), ez, clip)
        capa.close()
        if parar:
            mini = mini.rotate(90, expand=True)
            zoom = zoom.rotate(90, expand=True)
        n_pag = self._doc.page_count if self._doc is not None else None
        return mini, zoom, n_pag, (papel_fisico(R.width, R.height)[0], acostada)


# =========================================================================
#  INTERFAZ GRAFICA (estilo moderno, claro / oscuro / automatico)
# =========================================================================
import json

# Paleta gris azulado suavizado: (claro, oscuro)
C = {
    "lat_ini": ("#EEF2F7", "#272D36"),     # degradado barra lateral (arriba)
    "lat_fin": ("#D6DFEA", "#1D2229"),     # degradado barra lateral (abajo)
    "lat_sel": ("#C3CFDF", "#353F4C"),     # item seleccionado
    "fondo": ("#F6F8FB", "#1A1E24"),
    "tarjeta": ("#FFFFFF", "#232931"),
    "borde": ("#E2E7EE", "#313844"),
    "linea": ("#EDF0F4", "#2C323B"),
    "texto": ("#1E2730", "#E7EBF0"),
    "texto2": ("#6A7685", "#9AA6B4"),
    "acento": ("#4C6F9F", "#7096C8"),
    "acento_h": ("#3F5F8B", "#5E84B6"),
    "suave": ("#E7ECF3", "#2C333D"),
    "suave_h": ("#DCE3EC", "#353D48"),
    "campo": ("#F4F6F9", "#1D2228"),
}
# Colores del tema (Apariencia › Color del tema). Cada clave: (claro, oscuro)
TEMAS = {
    "Azul gris": dict(C),
    "Verde gris": {  # basado en #9FB0A6
        "lat_ini": ("#EEF3F0", "#27302C"), "lat_fin": ("#D2DED7", "#1D2421"), "lat_sel": ("#BFD0C6", "#36423C"),
        "fondo": ("#F5F8F6", "#1A1F1D"), "tarjeta": ("#FFFFFF", "#232A27"), "borde": ("#DCE5E0", "#323C37"),
        "linea": ("#ECF1EE", "#2C3531"), "texto": ("#1F2A25", "#E6ECE8"), "texto2": ("#66766D", "#9FB0A6"),
        "acento": ("#5F7D6C", "#6F8A7B"), "acento_h": ("#4F6B5C", "#62796C"), "suave": ("#E5EDE8", "#2C3531"),
        "suave_h": ("#D8E3DC", "#36403B"), "campo": ("#F2F6F3", "#1D2321"),
    },
}


def tema_guardado():
    """Nombre del color del tema guardado en las preferencias."""
    import json as _json
    base = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) else os.path.dirname(os.path.abspath(__file__))
    for carpeta in (base, os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "PdFOL")):
        try:
            with open(os.path.join(carpeta, "PdFOL_perfiles.json"), encoding="utf-8") as f:
                t_ = _json.load(f).get("tema", "Azul gris")
            return t_ if t_ in TEMAS else "Azul gris"
        except Exception:
            pass
    return "Azul gris"


def aplicar_tema(nombre):
    """Cambia la paleta antes de armar la ventana."""
    C.update(TEMAS.get(nombre, TEMAS["Azul gris"]))


ICONOS = [  # clave, titulo, color del icono, grupo, texto corto (barra de arriba)
    ("abrir", "Abrir", "#2563EB", 0, "Abrir"),
    ("documento", "Documento", "#3B82F6", 0, "Documento"),
    ("organizar", "Organizar y unir", "#06B6D4", 0, "Organizar"),
    ("imprimir", "Imprimir", "#6366F1", 0, "Imprimir"),
    ("comparar", "Comparar", "#0D9488", 0, "Comparar"),
    ("firmar", "Firmar y sellar", "#7C3AED", 0, "Firmar"),
    ("texto", "Texto", "#0284C7", 0, "Texto"),
    ("aplanar", "Aplanar", "#8B5CF6", 1, "Aplanar"),
    ("foliar", "Foliar", "#F59E0B", 1, "Foliar"),
    ("comprimir", "Comprimir", "#10B981", 1, "Comprimir"),
    ("perfiles", "Perfiles", "#EC4899", 2, "Perfiles"),
    ("apariencia", "Apariencia", "#64748B", 2, "Apariencia"),
]
ACCIONES = {"abrir"}                 # botones que no son una pagina (hacen algo)
PROXIMAMENTE = {}  # botones que todavia no hacen nada (ninguno)
EN_PANEL = {"aplanar", "foliar", "comprimir", "firmar", "texto"}  # se abren en el panel derecho, junto al documento
COLORES_FOLIO = [
    ("Negro", (0, 0, 0)), ("Grafito", (64, 72, 84)), ("Azul", (0, 70, 200)),
    ("Azul marino", (18, 40, 100)), ("Rojo", (200, 0, 0)), ("Vino", (128, 20, 40)),
    ("Verde", (0, 120, 60)), ("Morado", (100, 40, 160)),
]
NIVELES_UI = {"Sin pérdida": "sin-perdida", "Equilibrada": "equilibrada", "Alta": "alta"}
AYUDA_NIVEL = {
    "Sin pérdida": "Idéntico al original. Solo optimiza la estructura interna del PDF.",
    "Equilibrada": "Imágenes a JPEG 85 con la misma resolución. Diferencia casi imperceptible.",
    "Alta": "Imágenes a JPEG 75 con la misma resolución. Archivo más liviano.",
}
MAX_PERFILES = 10


# ------------------------------------------------------------------ perfiles
def _carpeta_config():
    base = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) \
        else os.path.dirname(os.path.abspath(__file__))
    try:
        prueba = os.path.join(base, ".pdfol_prueba")
        with open(prueba, "w") as f:
            f.write("ok")
        os.remove(prueba)
        return base
    except Exception:
        alt = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "PdFOL")
        os.makedirs(alt, exist_ok=True)
        return alt


class AlmacenPerfiles:
    """Hasta 10 perfiles + preferencias, en PdFOL_perfiles.json junto al programa."""

    def __init__(self):
        self.ruta = os.path.join(_carpeta_config(), "PdFOL_perfiles.json")
        self.datos = {"perfiles": [None] * MAX_PERFILES, "ultimo": None, "apariencia": "Automático"}
        try:
            with open(self.ruta, encoding="utf-8") as f:
                d = json.load(f)
            per = (d.get("perfiles") or [])[:MAX_PERFILES]
            self.datos["perfiles"] = per + [None] * (MAX_PERFILES - len(per))
            self.datos["ultimo"] = d.get("ultimo")
            self.datos["apariencia"] = d.get("apariencia", "Automático")
            for k_, v_ in d.items():  # otras preferencias (por ejemplo, miniaturas visibles)
                self.datos.setdefault(k_, v_)
        except Exception:
            pass

    def guardar(self):
        try:
            tmp = self.ruta + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(self.datos, f, ensure_ascii=False, indent=2)
            os.replace(tmp, self.ruta)
            return True
        except Exception:
            return False

    @property
    def perfiles(self):
        return self.datos["perfiles"]


# ------------------------------------------------------------------ dibujos
def _hex(c):
    c = c.lstrip("#")
    return tuple(int(c[i:i + 2], 16) for i in (0, 2, 4))


def _arco(cx, cy, r, a0, a1, n=14):
    """Puntos de un arco (grados; 0 = derecha, sentido horario en pantalla)."""
    return [(cx + r * math.cos(math.radians(a0 + (a1 - a0) * k / n)),
             cy + r * math.sin(math.radians(a0 + (a1 - a0) * k / n))) for k in range(n + 1)]


def _espejo(trazos):
    return [[(24 - x, y) for x, y in t] for t in trazos]


def _rect(x0, y0, x1, y1):
    return [(x0, y0), (x1, y0), (x1, y1), (x0, y1), (x0, y0)]


# v3.0: glifos de la cinta (trazos en una grilla de 24 x 24)
_DESHACER = [[(9, 14), (4, 9), (9, 4)], [(4, 9), (14.5, 9)] + _arco(14.5, 14.5, 5.5, -90, 90)[1:] + [(11, 20)]]
_GIRAR_DER = [_arco(12, 12.5, 7.5, -40, 250, 18), [(13.5, 3.2), (18, 6.6), (13.8, 9.6)]]
GLIFOS = {
    "guardar": [[(5, 4), (16, 4), (19, 7), (19, 20), (5, 20), (5, 4)], [(8, 4), (8, 9), (15, 9), (15, 4)],
                [(8, 20), (8, 14), (16, 14), (16, 20)]],
    "deshacer": _DESHACER,
    "rehacer": _espejo(_DESHACER),
    "seleccionar": [[(6.5, 3.5), (18, 12), (12.5, 13.5), (9.5, 20), (6.5, 3.5)]],
    "mano": [[(8, 14), (8, 6.5)], [(11, 12), (11, 4.5)], [(14, 12), (14, 5)], [(17, 13), (17, 7.5)],
             [(8, 14), (8, 16), (10.5, 20), (15.5, 20.5), (17, 17), (17, 13)]],
    "ancho": [[(3, 12), (21, 12)], [(7, 8), (3, 12), (7, 16)], [(17, 8), (21, 12), (17, 16)]],
    "pagina": [_rect(6, 3, 18, 21), [(9, 8), (15, 8)], [(9, 12), (15, 12)], [(9, 16), (13, 16)]],
    "girar_der": _GIRAR_DER,
    "girar_izq": _espejo(_GIRAR_DER),
    "una": [_rect(6, 3, 18, 21)],
    "continua": [_rect(7, 2, 17, 11), _rect(7, 13, 17, 22)],
    "dos": [_rect(2.5, 5, 11, 19), _rect(13, 5, 21.5, 19)],
    "miniaturas": [_rect(4, 4, 11, 11), _rect(13, 4, 20, 11), _rect(4, 13, 11, 20), _rect(13, 13, 20, 20)],
    "marcadores": [[(6.5, 3), (17.5, 3), (17.5, 21), (12, 17), (6.5, 21), (6.5, 3)]],
    "buscar": [_arco(10.5, 10.5, 6.5, 0, 360, 24), [(15.5, 15.5), (21, 21)]],
    "completa": [[(4, 9), (4, 4), (9, 4)], [(15, 4), (20, 4), (20, 9)], [(4, 15), (4, 20), (9, 20)],
                 [(15, 20), (20, 20), (20, 15)]],
    "impresa": [_rect(6, 3, 18, 21), [(3.5, 7), (3.5, 7.2)], [(3.5, 12), (3.5, 12.2)], [(3.5, 17), (3.5, 17.2)],
                [(9, 9), (15, 9)], [(9, 13), (15, 13)]],
    "resaltar": [[(9, 11), (4, 16), (4, 20), (8, 20), (13, 15)], [(9, 11), (15, 5), (19, 9), (13, 15), (9, 11)]],
    "cambiar": [[(4, 7), (15, 7)], [(4, 12), (11, 12)], [(4, 17), (9, 17)],
                [(13, 18), (13, 15.5), (18.5, 10), (21, 12.5), (15.5, 18), (13, 18)]],
    "agregar": [[(4, 6), (4, 4), (16, 4), (16, 6)], [(10, 4), (10, 20)], [(7, 20), (13, 20)], [(18, 13), (18, 21)],
                [(14, 17), (22, 17)]],
    "inicio": [[(3, 11), (12, 4), (21, 11)], [(6, 9), (6, 20), (18, 20), (18, 9)]],
    "firmar": [[(3, 16), (5.5, 13), (7, 8.5), (9, 7.5), (10, 11.5), (9, 17), (12, 13.5), (14, 15.5), (16, 12.5),
                (18.5, 15)], [(3, 20.5), (21, 20.5)]],
    "ant": [_arco(12, 12, 9, 0, 360, 28), [(8, 12.5), (12, 8.5), (16, 12.5)], [(12, 8.5), (12, 16.5)]],
    "sig": [_arco(12, 12, 9, 0, 360, 28), [(8, 11.5), (12, 15.5), (16, 11.5)], [(12, 7.5), (12, 15.5)]],
    "zoom_menos": [_arco(12, 12, 9, 0, 360, 28), [(8, 12), (16, 12)]],
    "zoom_mas": [_arco(12, 12, 9, 0, 360, 28), [(8, 12), (16, 12)], [(12, 8), (12, 16)]],
    "carpeta": [[(3, 7.5), (3, 18.5), (21, 18.5), (21, 9), (11.5, 9), (9.5, 6.5), (3, 6.5), (3, 7.5)]],
    "impresora": [[(7, 9), (7, 4), (17, 4), (17, 9)], [(7, 17), (4, 17), (4, 10), (20, 10), (20, 17), (17, 17)],
                  _rect(7, 14, 17, 20)],
    "disco": [[(5, 4), (16, 4), (19, 7), (19, 20), (5, 20), (5, 4)], [(8, 4), (8, 9), (15, 9), (15, 4)],
              [(8, 20), (8, 14), (16, 14), (16, 20)]],
    "herramientas": [[(14.5, 6), (18, 2.5), (21.5, 6), (18, 9.5), (14.5, 6)], [(16, 8), (5, 19), (5, 21), (7, 21),
                                                                           (18, 10)], _rect(3, 3, 9, 9),
                     _rect(15, 15, 21, 21)],
}


def _icono(clave, color, tam=30, escala=4, glifo=(255, 255, 255), sin_fondo=False):
    """Icono redondeado con glifo blanco (dibujado, sin archivos externos).
    v3.2: sin_fondo dibuja solo el trazo, mas grande (para la barra estilo Adobe)."""
    T = tam * escala
    img = Image.new("RGBA", (T, T), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    if sin_fondo and clave in GLIFOS:
        w = tuple(glifo) + (255,)
        k_ = T / 24 * 0.92
        o_ = T * 0.04
        for tr in GLIFOS[clave]:
            pts = [(o_ + x * k_, o_ + y * k_) for x, y in tr]
            if len(pts) == 2 and pts[0] == pts[1]:
                pts[1] = (pts[1][0] + 0.1, pts[1][1])
            d.line(pts, fill=w, width=max(2, int(T * 0.068)), joint="curve")
            for q in (pts[0], pts[-1]):
                rr = max(1, int(T * 0.034))
                d.ellipse([q[0] - rr, q[1] - rr, q[0] + rr, q[1] + rr], fill=w)
        return img.resize((tam, tam), Image.LANCZOS)
    r, g, b = _hex(color)
    arriba = tuple(min(255, int(v + (255 - v) * 0.18)) for v in (r, g, b))
    for y in range(T):  # degradado suave dentro del icono
        t = y / T
        col = tuple(int(arriba[i] * (1 - t) + (r, g, b)[i] * t) for i in range(3)) + (255,)
        d.line([(0, y), (T, y)], fill=col)
    mask = Image.new("L", (T, T), 0)
    ImageDraw.Draw(mask).rounded_rectangle([0, 0, T - 1, T - 1], radius=int(T * 0.24), fill=255)
    img.putalpha(mask)
    d = ImageDraw.Draw(img)
    w = tuple(glifo) + (255,)
    s = T / 30.0
    lw = max(2, int(2.2 * s))
    if clave in GLIFOS:  # v3.0: glifos de trazos (24 x 24, con margen)
        k_ = T / 24 * 0.66
        o_ = T * 0.17
        for tr in GLIFOS[clave]:
            pts = [(o_ + x * k_, o_ + y * k_) for x, y in tr]
            if len(pts) == 2 and pts[0] == pts[1]:
                pts[1] = (pts[1][0] + 0.1, pts[1][1])
            d.line(pts, fill=w, width=max(2, int(1.9 * s)), joint="curve")
            for q in (pts[0], pts[-1]):  # puntas redondeadas
                rr = max(1, int(0.95 * s))
                d.ellipse([q[0] - rr, q[1] - rr, q[0] + rr, q[1] + rr], fill=w)
        return img.resize((tam, tam), Image.LANCZOS)
    if clave == "documento":
        d.polygon([(9 * s, 6 * s), (17.5 * s, 6 * s), (22 * s, 10.5 * s), (22 * s, 24 * s), (9 * s, 24 * s)], outline=w, width=lw)
        d.line([(17.5 * s, 6 * s), (17.5 * s, 10.5 * s), (22 * s, 10.5 * s)], fill=w, width=lw)
        for yy in (14.5, 18, 21):
            d.line([(12 * s, yy * s), (19 * s, yy * s)], fill=w, width=max(1, lw - 1))
    elif clave == "aplanar":
        for k, yy in enumerate((9.5, 14, 18.5)):
            pts = [(15 * s, (yy - 3.5) * s), (23 * s, yy * s), (15 * s, (yy + 3.5) * s), (7 * s, yy * s)]
            d.polygon(pts, fill=w if k == 0 else None, outline=w, width=lw if k else 1)
    elif clave == "foliar":
        for xx in (12.5, 17.5):
            d.line([(xx * s + 1.2 * s, 7 * s), (xx * s - 1.2 * s, 23 * s)], fill=w, width=lw)
        for yy in (12, 18):
            d.line([(8 * s, yy * s), (22.5 * s, yy * s)], fill=w, width=lw)
    elif clave == "comprimir":
        d.line([(15 * s, 5.5 * s), (15 * s, 12 * s)], fill=w, width=lw)
        d.polygon([(11 * s, 9.5 * s), (19 * s, 9.5 * s), (15 * s, 13.5 * s)], fill=w)
        d.line([(15 * s, 24.5 * s), (15 * s, 18 * s)], fill=w, width=lw)
        d.polygon([(11 * s, 20.5 * s), (19 * s, 20.5 * s), (15 * s, 16.5 * s)], fill=w)
        d.line([(8 * s, 15 * s), (22 * s, 15 * s)], fill=w, width=max(1, lw - 1))
    elif clave == "organizar":
        for xx, yy in ((7.5, 7.5), (16, 7.5), (7.5, 16), (16, 16)):
            d.rounded_rectangle([xx * s, yy * s, (xx + 6.5) * s, (yy + 6.5) * s], radius=int(1.4 * s),
                                outline=w, width=max(1, lw - 1), fill=w if (xx, yy) == (16, 16) else None)
    elif clave == "perfiles":
        d.polygon([(10 * s, 6 * s), (20 * s, 6 * s), (20 * s, 24 * s), (15 * s, 19.5 * s), (10 * s, 24 * s)], fill=w)
    elif clave == "apariencia":
        d.ellipse([7.5 * s, 7.5 * s, 22.5 * s, 22.5 * s], outline=w, width=lw)
        d.pieslice([7.5 * s, 7.5 * s, 22.5 * s, 22.5 * s], 90, 270, fill=w)
    elif clave == "firmar":  # firma sobre una raya
        d.line([(6 * s, 23 * s), (24 * s, 23 * s)], fill=w, width=max(1, lw - 1))
        d.line([(6.5 * s, 18.5 * s), (8.5 * s, 10 * s), (10.5 * s, 17.5 * s), (13 * s, 9 * s), (15 * s, 17 * s),
                (17.5 * s, 12.5 * s), (19.5 * s, 16.5 * s), (23.5 * s, 13.5 * s)], fill=w, width=lw, joint="curve")
    elif clave == "texto":  # T con cursor
        d.line([(7 * s, 8 * s), (19 * s, 8 * s)], fill=w, width=lw + 1)
        d.line([(13 * s, 8 * s), (13 * s, 23 * s)], fill=w, width=lw + 1)
        d.line([(22.5 * s, 11 * s), (22.5 * s, 23 * s)], fill=w, width=max(1, lw - 1))
        d.line([(20.5 * s, 11 * s), (24.5 * s, 11 * s)], fill=w, width=max(1, lw - 1))
        d.line([(20.5 * s, 23 * s), (24.5 * s, 23 * s)], fill=w, width=max(1, lw - 1))
    elif clave == "abrir":  # carpeta
        d.polygon([(6 * s, 9 * s), (12 * s, 9 * s), (14 * s, 11 * s), (24 * s, 11 * s), (24 * s, 22.5 * s),
                   (6 * s, 22.5 * s)], outline=w, width=lw)
        d.polygon([(6 * s, 22.5 * s), (9 * s, 14.5 * s), (26 * s, 14.5 * s), (23.5 * s, 22.5 * s)], fill=w)
    elif clave == "imprimir":  # impresora
        d.rectangle([10 * s, 5.5 * s, 20 * s, 11 * s], outline=w, width=lw)
        d.rounded_rectangle([6 * s, 11 * s, 24 * s, 20 * s], radius=int(2 * s), fill=w)
        d.rectangle([10 * s, 17 * s, 20 * s, 24.5 * s], fill=(255, 255, 255, 255), outline=w)
        d.line([(12 * s, 20 * s), (18 * s, 20 * s)], fill=(r, g, b, 255), width=max(1, lw - 1))
        d.line([(12 * s, 22.5 * s), (18 * s, 22.5 * s)], fill=(r, g, b, 255), width=max(1, lw - 1))
    elif clave == "comparar":  # dos hojas lado a lado
        for x0_ in (6, 16):
            d.rounded_rectangle([x0_ * s, 7 * s, (x0_ + 8) * s, 23 * s], radius=int(1.4 * s), outline=w,
                                width=max(1, lw - 1), fill=w if x0_ == 16 else None)
    elif clave == "unir":  # dos hojas y un +
        d.rectangle([7 * s, 6 * s, 16 * s, 18 * s], outline=w, width=max(1, lw - 1))
        d.rectangle([12 * s, 11 * s, 21 * s, 23 * s], fill=w)
        d.line([(24 * s, 7 * s), (24 * s, 13 * s)], fill=w, width=lw)
        d.line([(21 * s, 10 * s), (27 * s, 10 * s)], fill=w, width=lw)
    elif clave == "ver":  # lupa
        d.ellipse([7 * s, 7 * s, 18 * s, 18 * s], outline=w, width=lw)
        d.line([(16.5 * s, 16.5 * s), (23 * s, 23 * s)], fill=w, width=lw + 1)
    elif clave == "visor":  # hoja con ojo
        d.rectangle([8 * s, 5 * s, 22 * s, 25 * s], outline=w, width=max(1, lw - 1))
        d.ellipse([10.5 * s, 12 * s, 19.5 * s, 18 * s], outline=w, width=max(1, lw - 1))
        d.ellipse([13.5 * s, 13.5 * s, 16.5 * s, 16.5 * s], fill=w)
    elif clave in ("girar_i", "girar_d"):  # flecha en arco
        d.arc([7 * s, 7 * s, 23 * s, 23 * s], 200 if clave == "girar_d" else -20, 520 if clave == "girar_d" else 300,
              fill=w, width=lw)
        if clave == "girar_d":
            d.polygon([(22 * s, 4.5 * s), (24.5 * s, 11 * s), (17.5 * s, 10 * s)], fill=w)
        else:
            d.polygon([(8 * s, 4.5 * s), (5.5 * s, 11 * s), (12.5 * s, 10 * s)], fill=w)
    elif clave in ("mover_i", "mover_d"):  # hoja con flecha
        izq = clave == "mover_i"
        d.rectangle([11 * s, 7 * s, 19 * s, 23 * s], outline=w, width=max(1, lw - 1))
        xa, xb = (9 * s, 3.5 * s) if izq else (21 * s, 26.5 * s)
        d.line([(xa, 15 * s), (xb + (2 * s if izq else -2 * s), 15 * s)], fill=w, width=lw)
        d.polygon([(xb, 15 * s), (xb + (4 * s if izq else -4 * s), 11.5 * s), (xb + (4 * s if izq else -4 * s), 18.5 * s)],
                  fill=w)
    elif clave == "mover_a":  # flecha hacia un numero
        d.line([(5 * s, 15 * s), (15 * s, 15 * s)], fill=w, width=lw)
        d.polygon([(17 * s, 15 * s), (13 * s, 11.5 * s), (13 * s, 18.5 * s)], fill=w)
        for xx in (19.5, 23.5):
            d.line([(xx * s + 0.8 * s, 8 * s), (xx * s - 0.8 * s, 22 * s)], fill=w, width=max(1, lw - 1))
        for yy in (12.5, 17.5):
            d.line([(17.5 * s, yy * s), (26 * s, yy * s)], fill=w, width=max(1, lw - 1))
    elif clave in ("deshacer", "rehacer"):  # flecha curva
        rh = clave == "rehacer"
        d.arc([7 * s, 9 * s, 23 * s, 24 * s], 180 if not rh else 270, 360 if not rh else 180 + 360, fill=w, width=lw)
        if rh:
            d.arc([7 * s, 9 * s, 23 * s, 24 * s], 180, 360, fill=w, width=lw)
            d.polygon([(23 * s, 8 * s), (27 * s, 16 * s), (19 * s, 16 * s)], fill=w)
        else:
            d.polygon([(7 * s, 8 * s), (3 * s, 16 * s), (11 * s, 16 * s)], fill=w)
    elif clave == "ayuda":  # signo de pregunta
        d.arc([10 * s, 5.5 * s, 20 * s, 15.5 * s], 180, 405, fill=w, width=lw)
        d.line([(16.6 * s, 14.4 * s), (15 * s, 16 * s), (15 * s, 19 * s)], fill=w, width=lw)
        d.ellipse([13.6 * s, 21.5 * s, 16.4 * s, 24.3 * s], fill=w)
    elif clave == "limpiar":  # papelera
        d.line([(7 * s, 9 * s), (23 * s, 9 * s)], fill=w, width=lw)
        d.line([(12.5 * s, 6 * s), (17.5 * s, 6 * s)], fill=w, width=lw)
        d.polygon([(9 * s, 11 * s), (21 * s, 11 * s), (19.5 * s, 24 * s), (10.5 * s, 24 * s)], outline=w, width=lw)
        for xx in (13, 17):
            d.line([(xx * s, 14 * s), (xx * s, 21 * s)], fill=w, width=max(1, lw - 1))
    return img.resize((tam, tam), Image.LANCZOS)


# ---- icono del programa (husky): PNG incluido en el codigo, asi el .exe no depende de archivos sueltos


def icono_husky(tam=64):
    import base64
    img = Image.open(io.BytesIO(base64.b64decode(ICONO_PNG_B64))).convert("RGBA")
    return img.resize((tam, tam), Image.LANCZOS) if img.size != (tam, tam) else img


# ---------------------------------------------------------------- v2.6: firmas, sellos y texto
MAX_FIRMAS = 5


def carpeta_firmas():
    d_ = os.path.join(_carpeta_config(), "PdFOL_firmas")
    os.makedirs(d_, exist_ok=True)
    return d_


def quitar_fondo_imagen(img, quitar=True, intensidad=50):
    """Firma o sello desde una foto: el papel (fondo claro) queda transparente y se recorta a lo dibujado.
    Busca el color del papel por zonas, asi las sombras de la foto no molestan."""
    from PIL import ImageFilter
    img = img.convert("RGBA")
    k = min(1.0, 1400 / max(img.size))
    if k < 1:
        img = img.resize((max(1, round(img.width * k)), max(1, round(img.height * k))), Image.LANCZOS)
    if quitar:
        rgb = img.convert("RGB")
        w, h = rgb.size
        B = max(8, round(max(w, h) / 36))
        peq = rgb.resize((max(1, -(-w // B)), max(1, -(-h // B))), Image.BOX)
        for _ in range(2):  # el papel: lo mas claro de los vecinos (los bloques llenos de tinta no cuentan)
            peq = peq.filter(ImageFilter.MaxFilter(3))
        fondo = peq.resize((w, h), Image.BILINEAR)
        r_, g_, b_ = ImageChops.subtract(fondo, rgb).split()
        dist = ImageChops.lighter(ImageChops.lighter(r_, g_), b_)
        t0 = 12 + (100 - intensidad) * 0.45
        t1 = t0 + 40
        alfa = dist.point(lambda v: 0 if v <= t0 else 255 if v >= t1 else int((v - t0) * 255 / (t1 - t0)))
        alfa = ImageChops.multiply(alfa, img.getchannel("A"))
        img = rgb.copy()
        img.putalpha(alfa)
    caja = img.getchannel("A").point(lambda v: 255 if v > 24 else 0).getbbox()
    if not caja:
        return None
    m_ = 4
    caja = (max(0, caja[0] - m_), max(0, caja[1] - m_), min(img.width, caja[2] + m_), min(img.height, caja[3] + m_))
    return img.crop(caja)


def fuente_parecida(flags, nombre):
    """Fuente base del PDF que mas se parece a la del texto original (para «Cambiar texto»)."""
    n_ = (nombre or "").lower()
    negrita = bool(flags & 16) or "bold" in n_ or "black" in n_ or "heavy" in n_
    cursiva = bool(flags & 2) or "italic" in n_ or "oblique" in n_
    if flags & 8 or "courier" in n_ or "mono" in n_ or "consol" in n_:
        return {(0, 0): "cour", (1, 0): "cobo", (0, 1): "coit", (1, 1): "cobi"}[(int(negrita), int(cursiva))]
    if flags & 4 or "times" in n_ or "serif" in n_ and "sans" not in n_ or "roman" in n_ or "georgia" in n_:
        return {(0, 0): "tiro", (1, 0): "tibo", (0, 1): "tiit", (1, 1): "tibi"}[(int(negrita), int(cursiva))]
    return {(0, 0): "helv", (1, 0): "hebo", (0, 1): "heit", (1, 1): "hebi"}[(int(negrita), int(cursiva))]


# ---------------------------------------------------------------- v2.7: fuentes para escribir y cambiar texto
# familia: ((normal, negrita, cursiva, negrita cursiva), interna parecida). Solo se ofrecen las que estan
# instaladas en Windows (o en la carpeta de fuentes del usuario); las «(PDF)» siempre estan.
FUENTES_ED = {
    "Arial": (("arial.ttf", "arialbd.ttf", "ariali.ttf", "arialbi.ttf"), "helv"),
    "Arial Narrow": (("ARIALN.TTF", "ARIALNB.TTF", "ARIALNI.TTF", "ARIALNBI.TTF"), "helv"),
    "Arial Black": (("ariblk.ttf", None, None, None), "helv"),
    "Calibri": (("calibri.ttf", "calibrib.ttf", "calibrii.ttf", "calibriz.ttf"), "helv"),
    "Calibri Light": (("calibril.ttf", None, "calibrili.ttf", None), "helv"),
    "Aptos": (("Aptos.ttf", "Aptos-Bold.ttf", "Aptos-Italic.ttf", "Aptos-Bold-Italic.ttf"), "helv"),
    "Segoe UI": (("segoeui.ttf", "segoeuib.ttf", "segoeuii.ttf", "segoeuiz.ttf"), "helv"),
    "Verdana": (("verdana.ttf", "verdanab.ttf", "verdanai.ttf", "verdanaz.ttf"), "helv"),
    "Tahoma": (("tahoma.ttf", "tahomabd.ttf", None, None), "helv"),
    "Trebuchet MS": (("trebuc.ttf", "trebucbd.ttf", "trebucit.ttf", "trebucbi.ttf"), "helv"),
    "Century Gothic": (("GOTHIC.TTF", "GOTHICB.TTF", "GOTHICI.TTF", "GOTHICBI.TTF"), "helv"),
    "Gill Sans MT": (("GIL_____.TTF", "GILB____.TTF", "GILI____.TTF", "GILBI___.TTF"), "helv"),
    "Franklin Gothic": (("framd.ttf", "FRADM.TTF", "framdit.ttf", "FRADMIT.TTF"), "helv"),
    "Candara": (("Candara.ttf", "Candarab.ttf", "Candarai.ttf", "Candaraz.ttf"), "helv"),
    "Corbel": (("corbel.ttf", "corbelb.ttf", "corbeli.ttf", "corbelz.ttf"), "helv"),
    "Times New Roman": (("times.ttf", "timesbd.ttf", "timesi.ttf", "timesbi.ttf"), "tiro"),
    "Cambria": (("cambria.ttc", "cambriab.ttf", "cambriai.ttf", "cambriaz.ttf"), "tiro"),
    "Georgia": (("georgia.ttf", "georgiab.ttf", "georgiai.ttf", "georgiaz.ttf"), "tiro"),
    "Garamond": (("GARA.TTF", "GARABD.TTF", "GARAIT.TTF", None), "tiro"),
    "Book Antiqua": (("BKANT.TTF", "ANTQUAB.TTF", "ANTQUAI.TTF", "ANTQUABI.TTF"), "tiro"),
    "Bookman Old Style": (("BOOKOS.TTF", "BOOKOSB.TTF", "BOOKOSI.TTF", "BOOKOSBI.TTF"), "tiro"),
    "Palatino Linotype": (("pala.ttf", "palab.ttf", "palai.ttf", "palabi.ttf"), "tiro"),
    "Constantia": (("constan.ttf", "constanb.ttf", "constani.ttf", "constanz.ttf"), "tiro"),
    "Century Schoolbook": (("SCHLBK.TTF", "SCHLBKB.TTF", "SCHLBKI.TTF", "SCHLBKBI.TTF"), "tiro"),
    "Courier New": (("cour.ttf", "courbd.ttf", "couri.ttf", "courbi.ttf"), "cour"),
    "Consolas": (("consola.ttf", "consolab.ttf", "consolai.ttf", "consolaz.ttf"), "cour"),
    "Lucida Console": (("lucon.ttf", None, None, None), "cour"),
    "Comic Sans MS": (("comic.ttf", "comicbd.ttf", "comici.ttf", "comicz.ttf"), "helv"),
    "Impact": (("impact.ttf", None, None, None), "helv"),
    "Helvetica (PDF)": (None, "helv"),
    "Times (PDF)": (None, "tiro"),
    "Courier (PDF)": (None, "cour"),
}
# nombres que usan los PDF para fuentes que en Windows se llaman distinto
ALIAS_FUENTE = {"helvetica": "Arial", "arialmt": "Arial", "timesroman": "Times New Roman", "times": "Times New Roman",
                "timesnewromanpsmt": "Times New Roman", "courier": "Courier New", "couriernewpsmt": "Courier New",
                "segoe": "Segoe UI", "gillsans": "Gill Sans MT", "franklingothic": "Franklin Gothic",
                "bookantiqua": "Book Antiqua", "palatino": "Palatino Linotype", "centuryschoolbook": "Century Schoolbook",
                "comicsans": "Comic Sans MS"}
_INTERNAS = {"helv": ("helv", "hebo", "heit", "hebi"), "tiro": ("tiro", "tibo", "tiit", "tibi"),
             "cour": ("cour", "cobo", "coit", "cobi")}
_LISTA_FUENTES = {}
_CACHE_FUENTE_ED = {}


def _archivo_fuente_ed(nombre):
    """Busca un archivo de fuente en las carpetas de Windows (sin distinguir mayusculas; la lista se lee una vez)."""
    if not nombre:
        return None
    for c in (_carpeta_fuentes(), os.path.join(os.environ.get("LOCALAPPDATA", ""), "Microsoft", "Windows", "Fonts")):
        if c not in _LISTA_FUENTES:
            try:
                _LISTA_FUENTES[c] = {f.lower(): os.path.join(c, f) for f in os.listdir(c)}
            except Exception:
                _LISTA_FUENTES[c] = {}
        p = _LISTA_FUENTES[c].get(nombre.lower())
        if p:
            return p
    return None


def fuentes_ed_disponibles():
    return [f for f, (arch, _b) in FUENTES_ED.items() if arch is None or _archivo_fuente_ed(arch[0])]


def fuente_ed(fam, neg=False, cur=False):
    """(archivo o None, nombre interno, fitz.Font) de la familia con negrita / cursiva (o lo mas parecido)."""
    clave = (fam, bool(neg), bool(cur))
    if clave in _CACHE_FUENTE_ED:
        return _CACHE_FUENTE_ED[clave]
    arch, base = FUENTES_ED.get(fam, FUENTES_ED["Helvetica (PDF)"])
    idx = (1 if neg else 0) + (2 if cur else 0)
    interna = _INTERNAS[base][idx]
    archivo = None
    if arch:
        for k_ in dict.fromkeys((idx, idx & 1, idx & 2, 0)):
            archivo = _archivo_fuente_ed(arch[k_])
            if archivo:
                break
    try:
        font = fitz.Font(fontfile=archivo) if archivo else fitz.Font(interna)
    except Exception:
        archivo, font = None, fitz.Font(interna)
    _CACHE_FUENTE_ED[clave] = (archivo, interna, font)
    return _CACHE_FUENTE_ED[clave]


def kw_fuente(it_):
    """Argumentos de fuente para insert_text / insert_textbox de PyMuPDF."""
    archivo, interna, _f = fuente_ed(it_.get("fam", "Helvetica (PDF)"), it_.get("neg"), it_.get("cur"))
    if not archivo:
        return {"fontname": interna}
    import zlib
    return {"fontname": "PdF%X" % (zlib.crc32(archivo.lower().encode()) & 0xFFFFFF), "fontfile": archivo}


def ancho_texto(txt, it_, tam=None):
    return fuente_ed(it_.get("fam", "Helvetica (PDF)"), it_.get("neg"), it_.get("cur"))[2].text_length(
        txt, fontsize=tam or it_["tam"])


def familia_de(nombre_pdf, flags=0):
    """La familia de la lista mas parecida a la fuente del texto original (la misma, si esta instalada)."""
    n_ = (nombre_pdf or "").split("+")[-1].lower()
    limpio = "".join(ch for ch in n_.split("-")[0].split(",")[0] if ch.isalpha())
    for sufijo in ("psmt", "mt", "ps", "regular", "bold", "italic", "oblique"):
        if limpio.endswith(sufijo) and len(limpio) > len(sufijo) + 2:
            limpio = limpio[: -len(sufijo)]
    disp = fuentes_ed_disponibles()
    mejor = None
    for fam in disp:
        k_ = "".join(ch for ch in fam.lower() if ch.isalpha())
        if limpio.startswith(k_) and (not mejor or len(k_) > len(mejor[1])):
            mejor = (fam, k_)
    if mejor:
        return mejor[0]
    for k_, fam in ALIAS_FUENTE.items():
        if limpio.startswith(k_) and fam in disp:
            return fam
    base = fuente_parecida(flags, nombre_pdf)
    return {"c": "Courier (PDF)", "t": "Times (PDF)"}.get(base[0], "Helvetica (PDF)")


def partir_renglones(txt, it_, ancho=None, con_fin=False):
    """Renglones del texto (ajustados al ancho, si hay). con_fin: (renglon, es_el_ultimo_del_parrafo)."""
    out = []
    for parr in txt.split("\n"):
        if not ancho:
            out.append((parr, True))
            continue
        lin = ""
        for pal in parr.split(" "):
            prueba = f"{lin} {pal}" if lin else pal
            if lin and ancho_texto(prueba, it_) > ancho:
                out.append((lin, False))
                lin = pal
            else:
                lin = prueba
        out.append((lin, True))
    return out if con_fin else [l_ for l_, _f in out]


INTERLINEADOS = {"Original": None, "1": 1.0, "1,15": 1.15, "1,5": 1.5, "2": 2.0}


def paso_renglon(it_):
    k_ = it_.get("interlin")
    if it_["tipo"] == "reemplazo":
        return it_["tam"] * k_ if k_ else it_["inter"]
    return it_["tam"] * (k_ or 1.25)


def diseno_texto(it_):
    """Donde va cada renglon (coordenadas de la pagina como se ve): [(x, base, texto, palabras_x o None)]."""
    tam, alin = it_["tam"], it_.get("alin", "izq")
    paso = paso_renglon(it_)
    if it_["tipo"] == "reemplazo":
        lineas = partir_renglones(it_["txt"], it_, it_.get("ancho"), con_fin=True)
        x0, base0 = it_["origen"]
        anchos = [ancho_texto(l_, it_) for l_, _f in lineas]
        caja = it_.get("ancho") or max(fitz.Rect(it_["rect_orig"]).x1 - x0, max(anchos + [0]))
    else:
        r_ = fitz.Rect(it_["rect"])
        x0, base0 = r_.x0 + tam * 0.3, r_.y0 + tam * 0.95
        if it_.get("ancho"):  # v4.1: recuadro de ancho fijo (el texto se acomoda en renglones)
            lineas = partir_renglones(it_["txt"], it_, it_["ancho"], con_fin=True)
        else:
            lineas = [(l_, True) for l_ in it_["txt"].split("\n")]
        anchos = [ancho_texto(l_, it_) for l_, _f in lineas]
        caja = it_.get("ancho") or max(anchos + [0])
    out = []
    for k_, ((l_, fin), w_) in enumerate(zip(lineas, anchos)):
        base = base0 + k_ * paso
        palabras = l_.split(" ")
        if alin == "just" and not fin and len(palabras) > 1:
            libre = caja - sum(ancho_texto(p_, it_) for p_ in palabras)
            hueco = libre / (len(palabras) - 1)
            xs, x_ = [], x0
            for p_ in palabras:
                xs.append((x_, p_))
                x_ += ancho_texto(p_, it_) + hueco
            out.append((x0, base, l_, xs, caja))
            continue
        dx = {"centro": (caja - w_) / 2, "der": caja - w_}.get(alin, 0)
        out.append((x0 + dx, base, l_, None, w_))
    return out


def dibujar_texto(pg, it_, conv, rot=0):
    """Escribe el texto de un item en la pagina. conv: punto de la vista -> punto de esta pagina."""
    c_ = tuple(v_ / 255 for v_ in it_["color"])
    tam, kw = it_["tam"], kw_fuente(it_)
    for x_, base, l_, palabras, w_ in diseno_texto(it_):
        if palabras:
            for xp, p_ in palabras:
                if p_:
                    pg.insert_text(conv((xp, base)), p_, fontsize=tam, color=c_, rotate=rot, **kw)
        elif l_:
            pg.insert_text(conv((x_, base)), l_, fontsize=tam, color=c_, rotate=rot, **kw)
        if not l_.strip():
            continue
        for marca, dy in (("sub", tam * 0.14), ("tach", -tam * 0.27)):
            if it_.get(marca):
                pg.draw_line(conv((x_, base + dy)), conv((x_ + w_, base + dy)), color=c_,
                             width=max(0.5, tam * 0.065))


def ruta_icono_ico():
    """Archivo .ico del husky (para la ventana y la barra de tareas de Windows)."""
    import tempfile
    p = os.path.join(tempfile.gettempdir(), f"PdFOL_{VERSION_INTERNA}_icono.ico")
    try:
        if not os.path.isfile(p):
            # v2.4: todos los tamanos que pide Windows con la pantalla escalada (125 %, 150 %, 200 %...)
            icono_husky(256).save(p, format="ICO", sizes=[(n_, n_) for n_ in (16, 20, 24, 30, 32, 36, 40, 48, 60,
                                                                               64, 72, 80, 96, 128, 256)])
        return p
    except Exception:
        return None


def _img_interruptor(encendido, oscuro, activo=True, w=44, h=24, escala=4):
    """Interruptor estilo macOS: riel redondeado con la perilla adentro."""
    W, H = w * escala, h * escala
    img = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    if encendido:
        riel = _hex(C["acento"][1 if oscuro else 0])
    else:
        riel = _hex("#3A4350" if oscuro else "#D3DBE5")
    alfa = 255 if activo else 110
    d.rounded_rectangle([0, 0, W - 1, H - 1], radius=H // 2, fill=riel + (alfa,))
    m = int(2.5 * escala)
    diam = H - 2 * m
    x0 = W - m - diam if encendido else m
    # sombra suave
    d.ellipse([x0, m + escala * 0.6, x0 + diam, m + diam + escala * 0.6], fill=(0, 0, 0, 45 if activo else 20))
    d.ellipse([x0, m, x0 + diam, m + diam], fill=(255, 255, 255, 255 if activo else 200))
    return img.resize((w, h), Image.LANCZOS)


def _miniatura_tema(modo, ancho=96, alto=64, escala=3):
    """Miniatura de ventana para el selector de apariencia (como en la foto)."""
    W, H = ancho * escala, alto * escala
    img = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    d = ImageDraw.Draw(img)
    claro = ("#F6F8FB", "#FFFFFF", "#D6DFEA", "#1E2730")
    oscuro = ("#1A1E24", "#232931", "#272D36", "#E7EBF0")

    def ventana(col, x0, x1):
        fondo, tarjeta, lateral, txt = col
        d.rounded_rectangle([x0, 0, x1, H - 1], radius=10 * escala // 2, fill=_hex(fondo))
        d.rectangle([x0 + 4, 14 * escala // 2 + 8, x0 + (x1 - x0) * 0.32, H - 6], fill=_hex(lateral))
        d.rounded_rectangle([x0 + (x1 - x0) * 0.38, 22 * escala // 2 + 8, x1 - 8, H - 10], radius=6, fill=_hex(tarjeta))

    if modo == "Claro":
        ventana(claro, 0, W - 1)
    elif modo == "Oscuro":
        ventana(oscuro, 0, W - 1)
    else:
        ventana(claro, 0, W - 1)
        mitad = Image.new("RGBA", (W, H), (0, 0, 0, 0))
        dd = ImageDraw.Draw(mitad)
        fondo, tarjeta, lateral, _ = oscuro
        dd.rounded_rectangle([0, 0, W - 1, H - 1], radius=10 * escala // 2, fill=_hex(fondo))
        dd.rounded_rectangle([W * 0.38, 22 * escala // 2 + 8, W - 9, H - 10], radius=6, fill=_hex(tarjeta))
        img.paste(mitad.crop((W // 2, 0, W, H)), (W // 2, 0), mitad.crop((W // 2, 0, W, H)))
    # botones de ventana estilo Windows (minimizar, maximizar, cerrar) a la derecha
    tinta = (120, 130, 145)
    y0, y1 = 5 * escala, 9 * escala
    xs = [W - 26 * escala, W - 17 * escala, W - 8 * escala]
    d.line([(xs[0], (y0 + y1) / 2), (xs[0] + 4 * escala, (y0 + y1) / 2)], fill=tinta, width=escala)
    d.rectangle([xs[1], y0, xs[1] + 4 * escala, y1], outline=tinta, width=escala)
    d.line([(xs[2], y0), (xs[2] + 4 * escala, y1)], fill=tinta, width=escala)
    d.line([(xs[2], y1), (xs[2] + 4 * escala, y0)], fill=tinta, width=escala)
    d.rounded_rectangle([0, 0, W - 1, H - 1], radius=10 * escala // 2, outline=(160, 170, 185), width=2)
    return img.resize((ancho, alto), Image.LANCZOS)


# ------------------------------------------------------------------ barra de titulo (Windows)
def _tenir_barra_titulo(ventana, oscuro):
    """Botones nativos de Windows (modernos en Win11) con la barra teñida al tema."""
    if os.name != "nt":
        return
    try:
        import ctypes
        ventana.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(ventana.winfo_id())
        dwm = ctypes.windll.dwmapi.DwmSetWindowAttribute
        valor = ctypes.c_int(1 if oscuro else 0)
        for attr in (20, 19):  # modo oscuro (Win10 2004+ / versiones anteriores)
            if dwm(hwnd, attr, ctypes.byref(valor), ctypes.sizeof(valor)) == 0:
                break
        r, g, b = _hex(C["lat_ini"][1 if oscuro else 0])
        cap = ctypes.c_int(r | (g << 8) | (b << 16))
        dwm(hwnd, 35, ctypes.byref(cap), ctypes.sizeof(cap))        # color de la barra (Win11)
        r, g, b = _hex(C["texto"][1 if oscuro else 0])
        txt = ctypes.c_int(r | (g << 8) | (b << 16))
        dwm(hwnd, 36, ctypes.byref(txt), ctypes.sizeof(txt))        # color del titulo (Win11)
        esquinas = ctypes.c_int(2)
        dwm(hwnd, 33, ctypes.byref(esquinas), ctypes.sizeof(esquinas))  # esquinas redondeadas (Win11)
    except Exception:
        pass


def es_instalado():
    """PdFOL instalado con el instalador (no el portable): tiene su desinstalador al lado."""
    return (os.name == "nt" and getattr(sys, "frozen", False)
            and os.path.isfile(os.path.join(os.path.dirname(sys.executable), "unins000.exe")))


ID_INSTALADOR = "{6C2E8B3A-41D7-4F5C-9A6E-3D0F5C1B2A20}_is1"


def anotar_version_instalada():
    """Version instalada: despues de actualizar, «Agregar o quitar programas» muestra la version nueva."""
    if not es_instalado():
        return
    try:
        import winreg
        k = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                           "Software\\Microsoft\\Windows\\CurrentVersion\\Uninstall\\" + ID_INSTALADOR, 0,
                           winreg.KEY_READ | winreg.KEY_SET_VALUE)
        if winreg.QueryValueEx(k, "DisplayVersion")[0] != VERSION_INTERNA:
            winreg.SetValueEx(k, "DisplayVersion", 0, winreg.REG_SZ, VERSION_INTERNA)
            winreg.SetValueEx(k, "DisplayName", 0, winreg.REG_SZ, f"PdFOL v{VERSION_INTERNA}")
    except Exception:
        pass
    try:  # v2.4: los PDF que abre PdFOL llevan su icono de documento (llega con la actualizacion)
        import winreg
        ico_doc = os.path.join(os.path.dirname(sys.executable), "PdFOL_documento.ico")
        if os.path.isfile(ico_doc):
            k = winreg.CreateKey(winreg.HKEY_CURRENT_USER, r"Software\Classes\PdFOL.PDF\DefaultIcon")
            try:
                actual_ = winreg.QueryValueEx(k, "")[0]
            except OSError:
                actual_ = ""
            if actual_ != ico_doc:
                winreg.SetValueEx(k, "", 0, winreg.REG_SZ, ico_doc)
                import ctypes
                ctypes.windll.shell32.SHChangeNotify(0x08000000, 0, None, None)  # SHCNE_ASSOCCHANGED
    except Exception:
        pass


def pdfol_abre_los_pdf():
    """True si Windows abre los .pdf con PdFOL (eleccion del usuario)."""
    if os.name != "nt":
        return False
    try:
        import winreg
        k = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                           r"Software\Microsoft\Windows\CurrentVersion\Explorer\FileExts\.pdf\UserChoice")
        return winreg.QueryValueEx(k, "ProgId")[0] == "PdFOL.PDF"
    except Exception:
        return False


def elegir_pdfol_para_pdf():
    """Abre la pantalla de Windows para elegir PdFOL como programa de los PDF.
    (Windows no deja que un programa se ponga solo como predeterminado: lo confirma el usuario.)"""
    import subprocess
    for destino in ("ms-settings:defaultapps?registeredAppUser=PdFOL", "ms-settings:defaultapps"):
        try:
            os.startfile(destino)
            return True
        except Exception:
            continue
    try:
        subprocess.Popen(["control", "/name", "Microsoft.DefaultPrograms"])
        return True
    except Exception:
        return False


def area_monitor(x, y, ventana=None):
    """v4.2: (izq, arriba, der, abajo) del area util del monitor donde esta el punto (x, y). Antes los menus
    y ventanitas se acomodaban solo a la pantalla principal y en un segundo monitor saltaban a la otra."""
    if os.name == "nt":
        try:
            import ctypes
            from ctypes import wintypes

            class _MONINFO(ctypes.Structure):
                _fields_ = [("cbSize", wintypes.DWORD), ("rcMonitor", wintypes.RECT), ("rcWork", wintypes.RECT),
                            ("dwFlags", wintypes.DWORD)]
            u32 = ctypes.windll.user32
            u32.MonitorFromPoint.restype = ctypes.c_void_p
            u32.MonitorFromPoint.argtypes = [wintypes.POINT, wintypes.DWORD]
            u32.GetMonitorInfoW.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
            hm = u32.MonitorFromPoint(wintypes.POINT(int(x), int(y)), 2)  # MONITOR_DEFAULTTONEAREST
            mi = _MONINFO()
            mi.cbSize = ctypes.sizeof(_MONINFO)
            if hm and u32.GetMonitorInfoW(hm, ctypes.byref(mi)):
                r_ = mi.rcWork
                return r_.left, r_.top, r_.right, r_.bottom
        except Exception:
            pass
    if ventana is not None:
        try:
            return 0, 0, ventana.winfo_screenwidth(), ventana.winfo_screenheight()
        except Exception:
            pass
    return -100000, -100000, 100000, 100000


def sombra_nativa(ventana):
    """v4.2: sombra de Windows para una ventanita sin bordes (como los menus de Windows 11)."""
    if os.name != "nt":
        return False
    try:
        import ctypes

        class _MARGENES(ctypes.Structure):
            _fields_ = [("l", ctypes.c_int), ("r", ctypes.c_int), ("t", ctypes.c_int), ("b", ctypes.c_int)]
        ventana.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(ventana.winfo_id()) or ventana.winfo_id()
        v_ = ctypes.c_int(2)  # DWMNCRP_ENABLED: que DWM dibuje el marco (y la sombra)
        ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 2, ctypes.byref(v_), ctypes.sizeof(v_))
        m_ = _MARGENES(1, 1, 1, 1)
        return ctypes.windll.dwmapi.DwmExtendFrameIntoClientArea(hwnd, ctypes.byref(m_)) == 0
    except Exception:
        return False


def icono_menu(cv_, clave, cx, cy, s, color, w=1.6):
    """v4.2: iconos de linea para los menus (dibujados en el lienzo: nitidos a cualquier escala)."""
    L = lambda *p_, **k: cv_.create_line(*[cx + a * s if i % 2 == 0 else cy + a * s for i, a in enumerate(p_)],
                                         fill=color, width=w, capstyle="round", joinstyle="round", tags="fila", **k)
    R = lambda x0, y0, x1, y1: cv_.create_rectangle(cx + x0 * s, cy + y0 * s, cx + x1 * s, cy + y1 * s,
                                                    outline=color, width=w, tags="fila")
    O = lambda x0, y0, x1, y1, **k: cv_.create_oval(cx + x0 * s, cy + y0 * s, cx + x1 * s, cy + y1 * s,
                                                    outline=color, width=w, tags="fila", **k)
    A = lambda x0, y0, x1, y1, ini, ext: cv_.create_arc(cx + x0 * s, cy + y0 * s, cx + x1 * s, cy + y1 * s,
                                                         start=ini, extent=ext, style="arc", outline=color, width=w,
                                                         tags="fila")
    if clave == "copiar":
        R(-0.55, -0.25, 0.25, 0.75)
        L(-0.25, -0.55, 0.55, -0.55, 0.55, 0.45)
    elif clave == "cortar":
        O(-0.75, 0.25, -0.25, 0.75)
        O(0.25, 0.25, 0.75, 0.75)
        L(-0.33, 0.33, 0.45, -0.75)
        L(0.33, 0.33, -0.45, -0.75)
    elif clave == "pegar":
        R(-0.6, -0.55, 0.6, 0.8)
        R(-0.28, -0.78, 0.28, -0.42)
        L(-0.3, 0.05, 0.3, 0.05)
        L(-0.3, 0.38, 0.15, 0.38)
    elif clave == "borrar":
        L(-0.7, -0.5, 0.7, -0.5)
        L(-0.25, -0.5, -0.2, -0.75, 0.2, -0.75, 0.25, -0.5)
        L(-0.5, -0.5, -0.4, 0.78, 0.4, 0.78, 0.5, -0.5)
        L(-0.13, -0.2, -0.13, 0.5)
        L(0.13, -0.2, 0.13, 0.5)
    elif clave == "imagen":
        R(-0.75, -0.6, 0.75, 0.6)
        L(-0.75, 0.45, -0.25, -0.05, 0.1, 0.3, 0.35, 0.08, 0.75, 0.45)
        O(0.2, -0.38, 0.45, -0.13)
    elif clave == "guardar":
        L(-0.65, -0.7, 0.4, -0.7, 0.7, -0.4, 0.7, 0.7, -0.65, 0.7, -0.65, -0.7)
        R(-0.35, -0.7, 0.3, -0.3)
        R(-0.4, 0.15, 0.4, 0.7)
    elif clave == "ocr":
        L(-0.75, -0.35, -0.75, -0.75, -0.35, -0.75)
        L(0.35, -0.75, 0.75, -0.75, 0.75, -0.35)
        L(-0.75, 0.35, -0.75, 0.75, -0.35, 0.75)
        L(0.35, 0.75, 0.75, 0.75, 0.75, 0.35)
        L(-0.4, -0.25, 0.4, -0.25)
        L(-0.4, 0.05, 0.4, 0.05)
        L(-0.4, 0.35, 0.15, 0.35)
    elif clave == "texto":
        L(-0.6, -0.65, 0.6, -0.65)
        L(0, -0.65, 0, 0.7)
        L(-0.25, 0.7, 0.25, 0.7)
    elif clave == "girar":
        A(-0.65, -0.65, 0.65, 0.65, 100, 270)
        L(0.05, -0.95, -0.15, -0.65, 0.15, -0.42)
    elif clave == "resaltar":
        L(-0.35, 0.35, 0.35, -0.55, 0.65, -0.25, -0.05, 0.65, -0.35, 0.35)
        L(-0.35, 0.35, -0.65, 0.65, -0.2, 0.65)
        L(-0.75, 0.85, 0.75, 0.85)
    elif clave == "pagina":
        L(-0.55, -0.8, 0.2, -0.8, 0.6, -0.4, 0.6, 0.8, -0.55, 0.8, -0.55, -0.8)
        L(0.2, -0.8, 0.2, -0.4, 0.6, -0.4)
    elif clave in ("buscar", "zoom_mas", "zoom_menos"):
        O(-0.7, -0.7, 0.35, 0.35)
        L(0.25, 0.25, 0.75, 0.75)
        if clave != "buscar":
            L(-0.4, -0.17, 0.05, -0.17)
            if clave == "zoom_mas":
                L(-0.17, -0.4, -0.17, 0.05)
    elif clave == "ancho":
        L(-0.8, 0, 0.8, 0)
        L(-0.5, -0.3, -0.8, 0, -0.5, 0.3)
        L(0.5, -0.3, 0.8, 0, 0.5, 0.3)
        L(-0.8, -0.75, -0.8, 0.75)
        L(0.8, -0.75, 0.8, 0.75)
    elif clave == "completa":
        L(-0.75, -0.3, -0.75, -0.75, -0.3, -0.75)
        L(0.3, -0.75, 0.75, -0.75, 0.75, -0.3)
        L(-0.75, 0.3, -0.75, 0.75, -0.3, 0.75)
        L(0.3, 0.75, 0.75, 0.75, 0.75, 0.3)
    elif clave == "abrir":
        L(-0.8, 0.6, -0.8, -0.6, -0.3, -0.6, -0.15, -0.4, 0.7, -0.4, 0.7, 0.6, -0.8, 0.6)
    elif clave == "mover":
        L(-0.75, 0, 0.75, 0)
        L(0, -0.75, 0, 0.75)
        L(-0.5, -0.25, -0.75, 0, -0.5, 0.25)
        L(0.5, -0.25, 0.75, 0, 0.5, 0.25)
    elif clave == "firma":
        L(-0.8, 0.5, -0.4, 0.1, -0.1, 0.45, 0.25, -0.1, 0.5, 0.25)
        L(-0.8, 0.8, 0.8, 0.8)
    elif clave == "agregar":
        L(-0.6, 0, 0.6, 0)
        L(0, -0.6, 0, 0.6)
    elif clave == "deshacer":
        A(-0.55, -0.45, 0.75, 0.75, 90, 180)
        L(-0.35, -0.75, -0.65, -0.45, -0.35, -0.15)
    elif clave == "imprimir":
        R(-0.75, -0.2, 0.75, 0.45)
        R(-0.45, -0.75, 0.45, -0.2)
        R(-0.45, 0.2, 0.45, 0.8)
    elif clave == "elegir":
        R(-0.7, -0.7, 0.7, 0.7)
        L(-0.35, 0.0, -0.1, 0.3, 0.4, -0.3)
    else:
        cv_.create_oval(cx - s * 0.18, cy - s * 0.18, cx + s * 0.18, cy + s * 0.18, fill=color, outline="", tags="fila")


def icono_para(texto):
    """Elige el icono del menu segun lo que dice el renglon."""
    t_ = texto.lower()
    for palabras, clave in ((("acercar", "agrandar"), "zoom_mas"), (("alejar", "achicar"), "zoom_menos"),
                            (("ajustar ancho", "ancho"), "ancho"), (("pantalla completa",), "completa"),
                            (("guardar",), "guardar"), (("reconocer", "ocr"), "ocr"), (("cortar",), "cortar"),
                            (("pegar",), "pegar"), (("imagen", "imágenes"), "imagen"),
                            (("copiar",), "copiar"), (("quitar", "borrar", "eliminar"), "borrar"),
                            (("girar", "rotar"), "girar"), (("resalt",), "resaltar"), (("buscar",), "buscar"),
                            (("abrir",), "abrir"), (("mover",), "mover"), (("firma", "sello"), "firma"),
                            (("deshacer",), "deshacer"), (("imprimir",), "imprimir"),
                            (("texto", "palabra", "renglón"), "texto"), (("agregar", "nuevo", "nueva"), "agregar"),
                            (("seleccionar", "elegir", "todo"), "elegir"),
                            (("página", "pagina", "hoja", "documento", "pdf"), "pagina")):
        if any(p_ in t_ for p_ in palabras):
            return clave
    return None


def esquinas_redondeadas(ventana):
    """Windows 11 redondea las esquinas de la ventanita (sin bordes dentados)."""
    if os.name != "nt":
        return
    try:
        import ctypes
        ventana.update_idletasks()
        hwnd = ctypes.windll.user32.GetParent(ventana.winfo_id()) or ventana.winfo_id()
        v_ = ctypes.c_int(2)  # DWMWCP_ROUND
        ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 33, ctypes.byref(v_), ctypes.sizeof(v_))
    except Exception:
        pass


# ------------------------------------------------------------------ interfaz
def iniciar_interfaz():
    _tiempo("librerias cargadas")
    import tkinter as tk
    from tkinter import filedialog, messagebox, colorchooser
    import customtkinter as ctk
    # v4.0: customtkinter, al pasar la ventana a otro monitor con otra escala, la vuelve casi transparente y
    # redibuja todo MIENTRAS se arrastra (se ve transparente y se pega). Ese control lo hace PdFOL: espera a
    # que se suelte la ventana y ajusta una sola vez (ver revisar_monitor)
    ctk.ScalingTracker.check_dpi_scaling = classmethod(lambda cls: None)

    pdfs_arg = [a_ for a_ in sys.argv[1:] if os.path.isfile(a_) and a_.lower().endswith(".pdf")]
    instancia = instancia_unica(pdfs_arg) if not os.environ.get("PDFOL_PRUEBA") else False
    if instancia is None:  # PdFOL ya estaba abierto: los PDF se abrieron alli como pestanas
        cerrar_pantalla_de_inicio()
        return
    # v3.0: los procesos que dibujan arrancan recien con la ventana a la vista: en Windows cada uno es otra
    # copia de PdFOL.exe y competian con el arranque. Mientras tanto la primera hoja la dibuja la ventana.
    q_pag, q_min, q_bus, q_sal = mp.Queue(), mp.Queue(), mp.Queue(), mp.Queue()
    procs_inicio = []
    for q_, f_ in ((q_pag, _proceso_render), (q_min, _proceso_render)):  # v2.6: el de buscar, despues
        try:
            procs_inicio.append(mp.Process(target=f_, args=(q_, q_sal), daemon=True))
        except Exception:
            pass

    def arrancar_procesos():
        for k_, pr_ in enumerate(procs_inicio):
            try:
                if pr_._popen is None:
                    pr_.start()
            except Exception:
                pass
    almacen = AlmacenPerfiles()
    aplicar_tema(almacen.datos.get("tema", "Azul gris"))
    modo_ini = almacen.datos.get("apariencia", "Automático")
    ctk.set_appearance_mode({"Claro": "light", "Oscuro": "dark"}.get(modo_ini, "system"))
    ctk.set_default_color_theme("blue")

    if os.name == "nt":  # barra de tareas: PdFOL con su propio icono (no el de Python)
        try:
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(f"PdFOL.PdFOL.{VERSION_INTERNA}")
        except Exception:
            pass
    raiz = ctk.CTk(fg_color=C["fondo"])
    # v3.3: escala de la pantalla de Windows (125 %, 150 %...). Los dibujos propios (barra de arriba, riel
    # derecho) se hacen a ese tamano, asi los iconos salen nitidos y del tamano justo
    try:
        S_UI = max(1.0, float(ctk.ScalingTracker.get_window_scaling(raiz)))
    except Exception:
        S_UI = 1.0
    escala = {"s": S_UI, "s0": S_UI, "geo": {}, "quieta": {}}
    try:
        escala["ts0"] = float(raiz.tk.call("tk", "scaling"))
    except Exception:
        escala["ts0"] = None

    def px(n):
        return int(round(n * escala["s"]))
    if _INICIO is not None:
        raiz.withdraw()  # la ventana aparece recien cuando esta completa (mientras, el husky)
    raiz.title(f"{NOMBRE} {VERSION} · by {AUTOR}")
    raiz.geometry("1320x860")
    raiz.minsize(1080, 720)

    def maximizar():
        try:
            if os.name == "nt":
                raiz.state("zoomed")
            else:
                raiz.attributes("-zoomed", True)
        except Exception:
            pass

    # ---- icono del husky en la ventana, la barra de tareas y todas las ventanitas
    ico_ruta = ruta_icono_ico()
    ico_fotos = []

    def icono_nitido(w):
        """v2.4: Tk carga el icono chico (32 px) y Windows lo estira en la barra de tareas: se ve borroso.
        Aca se le da a la ventana el tamano exacto que usa Windows para esta pantalla."""
        try:
            import ctypes
            u32 = ctypes.windll.user32
            u32.LoadImageW.restype = ctypes.c_void_p
            u32.SendMessageW.argtypes = [ctypes.c_void_p, ctypes.c_uint, ctypes.c_void_p, ctypes.c_void_p]
            u32.GetParent.restype = ctypes.c_void_p
            hwnd = u32.GetParent(w.winfo_id()) or w.winfo_id()
            try:
                dpi = u32.GetDpiForWindow(ctypes.c_void_p(hwnd)) or 96
            except Exception:
                dpi = 96
            for tipo_, metrica_, base_ in ((1, 11, 32), (0, 49, 16)):  # ICON_BIG/SM_CXICON, ICON_SMALL/SM_CXSMICON
                try:
                    n_ = u32.GetSystemMetricsForDpi(metrica_, dpi)
                except Exception:
                    n_ = 0
                n_ = n_ or round(base_ * dpi / 96)
                if tipo_ == 1:
                    n_ = max(n_, 48)  # la barra de tareas usa el grande: mejor que sobre a que falte
                h_ = u32.LoadImageW(None, ico_ruta, 1, n_, n_, 0x10)  # IMAGE_ICON, LR_LOADFROMFILE
                if h_:
                    u32.SendMessageW(hwnd, 0x80, ctypes.c_void_p(tipo_), ctypes.c_void_p(h_))  # WM_SETICON
        except Exception:
            pass

    def poner_icono(w):
        try:
            if not w.winfo_exists():
                return
            if os.name == "nt" and ico_ruta:
                w.iconbitmap(ico_ruta)
                icono_nitido(w)
            else:
                if not ico_fotos:
                    from PIL import ImageTk
                    ico_fotos.extend([ImageTk.PhotoImage(icono_husky(64)), ImageTk.PhotoImage(icono_husky(32))])
                w.iconphoto(False, *ico_fotos)
        except Exception:
            pass

    poner_icono(raiz)
    raiz.after(260, lambda: poner_icono(raiz))  # CustomTkinter pone el suyo a los 200 ms
    _init_toplevel = ctk.CTkToplevel.__init__

    def _toplevel_con_icono(self, *a, **k):
        _init_toplevel(self, *a, **k)
        poner_icono(self)
        self.after(260, lambda: poner_icono(self))

    ctk.CTkToplevel.__init__ = _toplevel_con_icono

    FAM = "Segoe UI" if os.name == "nt" else "DejaVu Sans"

    def F(tam=13, peso="normal"):
        return ctk.CTkFont(family=FAM, size=tam, weight=peso)

    eventos = queue.Queue()
    cancelar = threading.Event()
    app = {"scores": None, "umbral": None, "ruta": None, "ocupado": False, "salida": None,
           "n_paginas": None, "color": (0, 0, 0), "prev_job": None, "pagina": "visor", "panel": None,
           "perfil": almacen.datos.get("ultimo"), "cargando": False, "modo_actual": None, "listas": set()}

    fuentes = fuentes_disponibles()

    # ---------------- variables
    V = {
        "ruta": tk.StringVar(),
        "apl": tk.BooleanVar(value=True), "fol": tk.BooleanVar(value=False), "comp": tk.BooleanVar(value=True),
        "dpi": tk.StringVar(value=str(DPI_DEFECTO)), "texto": tk.BooleanVar(value=True),
        "nucleos": tk.StringVar(value="Automático"), "extra": tk.StringVar(), "excluir": tk.StringVar(),
        "nivel": tk.StringVar(value="Equilibrada"),
        "inicio": tk.StringVar(value="1"), "digitos": tk.StringVar(value="4"),
        "desde": tk.StringVar(value="1"), "hasta": tk.StringVar(value=""),
        "formato": tk.StringVar(value="Solo número"), "prefijo": tk.StringVar(value="Folio"),
        "prefijo_txt": tk.StringVar(value=""),
        "fuente": tk.StringVar(value=fuentes[0] if fuentes else "Helvetica (interna)"),
        "tam": tk.StringVar(value="12"), "negrita": tk.BooleanVar(value=False),
        "pos": tk.StringVar(value="Abajo derecha"),
        "mh": tk.StringVar(value="10"), "mv": tk.StringVar(value="10"),
        "apariencia": tk.StringVar(value=modo_ini),
    }
    v_estado = tk.StringVar(value="Elegí un PDF para empezar.")
    v_detalle = tk.StringVar(value="")
    v_ejemplo = tk.StringVar(value="")
    v_prev_info = tk.StringVar(value="")
    v_info_doc = tk.StringVar(value="Ningún documento seleccionado.")
    v_info_apl = tk.StringVar(value="Presioná «Analizar» para detectar los planos pesados.")
    v_perfil_lbl = tk.StringVar(value="")

    # ================================================== ESTRUCTURA
    # fila 0: barra de arriba · fila 1: pestanas · fila 2: contenido · fila 3: barra de abajo
    raiz.grid_columnconfigure(0, weight=1)
    raiz.grid_rowconfigure(3, weight=1)

    def foto_tk(pil):
        import base64
        b = io.BytesIO()
        pil.save(b, "PNG")
        return tk.PhotoImage(data=base64.b64encode(b.getvalue()).decode("ascii"))

    def modo_oscuro():
        return ctk.get_appearance_mode().lower() == "dark"

    def col(clave):
        return C[clave][1 if modo_oscuro() else 0]

    # ---- v3.2: arriba, como Adobe Acrobat: la hoja ocupa casi todo.
    # Fila 1 (36 px): husky, «Inicio», «Herramientas» y las pestanas de los documentos; a la derecha, buscar.
    # Fila 2 (44 px): una sola barra de iconos chicos (sin textos; al pasar el mouse dicen que hacen).
    ALTO_SUP = px(36)
    superior = tk.Canvas(raiz, height=ALTO_SUP, highlightthickness=0, bd=0)
    superior.grid(row=0, column=0, sticky="ew")
    import tkinter.font as tkfont
    f_item = tkfont.Font(family=FAM, size=10)
    logo_tk = foto_tk(icono_husky(px(24)))

    def _icono_apagado(img):
        a = img.getchannel("A").point(lambda v: v * 0.38)
        img = img.copy()
        img.putalpha(a)
        return img
    e_buscar = ctk.CTkEntry(superior, width=220, height=26, corner_radius=13, font=F(12), bg_color=C["lat_ini"],
                            fg_color=C["campo"], border_color=C["borde"], text_color=C["texto"],
                            placeholder_text="Buscar  (Ctrl+F)", placeholder_text_color=C["texto2"])
    caja_pest = tk.Frame(superior, bd=0, highlightthickness=0, height=34)
    app["vista_top"] = None  # None: el documento · "inicio" · "herr"
    X_PEST = 300

    def dibujar_superior(*_):
        superior.delete("all")
        w = max(superior.winfo_width(), 900)
        h = px(36)
        superior.configure(bg=col("lat_ini"))
        if caja_pest.cget("bg") != col("lat_ini"):
            try:
                tk.Frame.configure(caja_pest, bg=col("lat_ini"))
            except Exception:
                pass
        superior.create_line(0, h - 1, w, h - 1, fill=col("borde"))
        if app.get("menu_logo"):
            superior.create_rectangle(2, 3, px(40), h - 3, fill=col("lat_sel"), outline="")
        superior.create_image(px(21), h // 2, image=logo_tk, tags=("item", "logo"))
        superior.create_rectangle(2, 3, px(40), h - 3, outline="", fill="", tags=("item", "logo"))
        if app.get("hay_nueva"):
            superior.create_oval(px(30), px(4), px(39), px(13), fill="#F97316", outline=col("lat_ini"), width=2,
                                 tags=("item", "logo"))
        x = px(46)
        try:
            sin_doc = not pest
        except NameError:  # todavia se esta armando la ventana
            sin_doc = True
        for clave_, txt_ in (("inicio", "Inicio"), ("herr", "Herramientas")):
            ancho_ = f_item.measure(txt_) + px(28)
            elegida = app["vista_top"] == clave_ or (clave_ == "inicio" and sin_doc and not app["vista_top"])
            if elegida:
                superior.create_rectangle(x, px(4), x + ancho_, h, fill=col("tarjeta"), outline=col("borde"))
                superior.create_line(x + 1, h - 1, x + ancho_, h - 1, fill=col("tarjeta"))
            superior.create_text(x + ancho_ / 2, h // 2 + 1, text=txt_, fill=col("texto"),
                                 font=(FAM, 10, "bold" if elegida else "normal"), tags=("item", "top:" + clave_))
            superior.create_rectangle(x, px(4), x + ancho_, h, outline="", fill="", tags=("item", "top:" + clave_))
            x += ancho_ + 2
        superior.create_line(x + 4, 9, x + 4, h - 9, fill=col("borde"))
        app["x_pest"] = x + 12
        ancho_b = 220 if w > 1100 else 170
        e_buscar.configure(width=ancho_b)
        superior.create_window(w - 10, h // 2, window=e_buscar, anchor="e")
        superior.create_window(app["x_pest"], h, window=caja_pest, anchor="sw")
        dibujar_cinta()

    def ir_top(clave_):
        app["vista_top"] = None if app["vista_top"] == clave_ and pest else clave_
        if app["pagina"] != "visor":
            mostrar_pagina("visor")
        mostrar_inicio()
        dibujar_superior()

    def click_superior(ev):
        for it in reversed(superior.find_overlapping(ev.x, ev.y, ev.x, ev.y)):
            tags_ = superior.gettags(it)
            if "logo" in tags_:
                menu_husky()
                return
            for t in tags_:
                if t.startswith("top:"):
                    ir_top(t[4:])
                    return

    superior.bind("<Configure>", dibujar_superior)
    superior.bind("<Button-1>", click_superior)

    # ---- la barra de iconos
    barra_pest = ctk.CTkFrame(raiz, fg_color=C["tarjeta"], corner_radius=0, height=44)
    barra_pest.grid(row=2, column=0, sticky="ew")
    barra_pest.grid_columnconfigure(0, weight=1)
    ALTO_CINTA = px(44)
    cinta = tk.Canvas(barra_pest, height=ALTO_CINTA, highlightthickness=0, bd=0, cursor="hand2")
    cinta.grid(row=0, column=0, sticky="ew")
    ctk.CTkFrame(raiz, height=1, fg_color=C["borde"], corner_radius=0).grid(row=2, column=0, sticky="sew")
    app["cinta"] = "Inicio"
    iconos_cinta = {}
    COLOR_ICONO = {c_: col_ for c_, _t, col_, *_r in ICONOS}
    COLOR_ICONO.update(resaltar="#EAB308", cambiar="#0284C7", agregar="#0284C7")
    v_pag_bar = tk.StringVar(value="")
    e_pag_bar = ctk.CTkEntry(cinta, textvariable=v_pag_bar, width=42, height=26, corner_radius=6, font=F(12),
                             justify="center", fg_color=C["campo"], border_color=C["borde"], text_color=C["texto"])
    e_pag_bar.bind("<Return>", lambda e: ir_inf("bar"))

    def icono_cinta(clave, color=None, tam=22):
        k_ = (clave, color, modo_oscuro(), tam)
        if k_ not in iconos_cinta:
            if color:
                im_ = _icono(clave, color, tam)
            else:  # icono de trazo, del color del texto, sin fondo (como Adobe)
                im_ = _icono(clave, col("tarjeta"), px(20), glifo=_hex(col("texto")), sin_fondo=True)
            iconos_cinta[k_] = foto_tk(im_)
        return iconos_cinta[k_]

    def cinta_items():
        """Grupos de iconos: (id, ayuda, icono, color o None, accion, elegido)."""
        t_ = pest_activa()
        v_ = vista_activa()
        modo_v = (t_ or {}).get("modo_vista", "continua")
        zoom_ = v_.zoom if v_ else None
        en_visor = app["pagina"] == "visor" and not app["vista_top"]
        panel = app.get("panel") if en_visor else None
        texto_modo = None
        try:
            texto_modo = v_tmodo.get()
        except Exception:
            pass
        sel_ = en_visor and v_herr.get() == "Seleccionar" and not vis["modo_res"] and not panel
        mano_ = en_visor and v_herr.get() == "Mano" and not vis["modo_res"] and not panel
        n_ = n_resaltes()
        izq = [[("guardar", "Guardar los cambios en el PDF (Ctrl+S)" + (f" · {n_} sin guardar" if n_ else ""),
                 "disco", None, lambda: guardar_resaltados_dialogo() if (n_resaltes() or (
                     pest_activa() and tiene_organizado(pest_activa()))) else
                 v_estado.set("No hay cambios sin guardar."), False),
                ("abrir", "Abrir PDF (Ctrl+O)", "carpeta", None, lambda: abrir_archivos(), False),
                ("imprimir", "Imprimir", "impresora", None, lambda: abrir_imprimir(), False),
                ("buscar", "Buscar en el documento (Ctrl+F)", "buscar", None, lambda: enfocar_busqueda(), False)]]
        centro = [[("ant", "Página anterior", "ant", None, lambda: ir_inf("ant"), False),
                   ("sig", "Página siguiente", "sig", None, lambda: ir_inf("sig"), False),
                   ("PAG", None, None, None, None, False)],
                  [("seleccionar", "Seleccionar texto", "seleccionar", None, lambda: cinta_herr("Seleccionar"), sel_),
                   ("mano", "Mano (mover la hoja)", "mano", None, lambda: cinta_herr("Mano"), mano_)],
                  [("menos", "Alejar", "zoom_menos", None, lambda: (vista_activa() and vista_activa().zoom_paso(-1)),
                    False),
                   ("mas", "Acercar", "zoom_mas", None, lambda: (vista_activa() and vista_activa().zoom_paso(1)),
                    False),
                   ("ZOOM", None, None, None, None, False),
                   ("ajuste", "Ajustar: al ancho / página entera", "ancho" if zoom_ != "Página entera" else "pagina",
                    None, lambda: menu_ajuste(), zoom_ in ("Ajustar ancho", "Página entera"))],
                  [("girar_izq", "Girar a la izquierda: esta página, todo el documento o solo la vista", "girar_izq",
                    None, lambda: menu_girar(-90), False),
                   ("girar_der", "Girar a la derecha: esta página, todo el documento o solo la vista", "girar_der",
                    None, lambda: menu_girar(90), False),
                   ("modo", "Vista: una página, continua o dos páginas",
                    {"una": "una", "dos": "dos", "mosaico": "dos"}.get(modo_v, "continua"), None, lambda: menu_modo(), modo_v != "continua")],
                  [("resaltar", "Resaltar", "resaltar", None, lambda: alternar_resaltar(), bool(vis["modo_res"])),
                   ("cambiar", "Cambiar texto del PDF", "cambiar", None, lambda: cinta_texto("Cambiar"),
                    panel == "texto" and texto_modo == "Cambiar"),
                   ("agregar", "Agregar texto", "agregar", None, lambda: cinta_texto("Agregar"),
                    panel == "texto" and texto_modo == "Agregar"),
                   ("firmar", "Firmar y sellar", "firmar", None, lambda: cinta_panel("firmar"), panel == "firmar")]]
        der = [[("deshacer", "Deshacer (Ctrl+Z)", "deshacer", None, cinta_deshacer, False),
                ("rehacer", "Rehacer (Ctrl+Y)", "rehacer", None, lambda: rehacer_edicion(), False),
                ("completa", "Pantalla completa (F11)", "completa", None, lambda: pantalla_completa(),
                 bool(app.get("completa")))]]
        return izq, centro, der

    def _ancho_item(it_):
        if it_[0] == "PAG":
            return px(50) + f_item.measure(v_tot_bar.get() or "/ 000") + px(6)
        if it_[0] == "ZOOM":
            return f_item.measure("000 % ▾") + px(12)
        return px(36)

    v_tot_bar = tk.StringVar(value="")
    v_pct_bar = tk.StringVar(value="")

    def dibujar_cinta(*_):
        cinta.delete("all")
        w = max(cinta.winfo_width(), 900)
        h = px(44)
        cinta.configure(bg=col("tarjeta"))
        try:
            izq, centro, der = cinta_items()
        except NameError:  # todavia se esta armando la ventana
            return
        app["cinta_acc"], app["cinta_ayuda"] = {}, {}
        hay_doc = bool(pest) and not app["vista_top"]

        def poner(grupos, x):
            for g_, grupo in enumerate(grupos):
                if g_:
                    cinta.create_line(x + 5, 11, x + 5, h - 11, fill=col("borde"))
                    x += 10
                for it_ in grupo:
                    id_, ayuda_, ico_, color_, acc_, elegido = it_
                    ancho_ = _ancho_item(it_)
                    if id_ == "PAG":
                        if hay_doc:
                            cinta.create_window(x + px(4), h // 2, window=e_pag_bar, anchor="w")
                            cinta.create_text(x + px(52), h // 2, text=v_tot_bar.get(), anchor="w", fill=col("texto2"),
                                              font=(FAM, 10))
                    elif id_ == "ZOOM":
                        cinta.create_text(x + ancho_ / 2, h // 2, text=(v_pct_bar.get() + " ▾") if hay_doc else "",
                                          fill=col("texto"), font=(FAM, 10), tags=("item", "b:zoom_menu"))
                        cinta.create_rectangle(x, 8, x + ancho_, h - 8, outline="", fill="", tags=("item", "b:zoom_menu"))
                        app["cinta_acc"]["zoom_menu"] = menu_zoom
                        app["cinta_ayuda"]["zoom_menu"] = "Zoom"
                    else:
                        if elegido:
                            x0, y0, x1, y1, r = x + 3, 6, x + ancho_ - 3, h - 6, 6
                            cinta.create_polygon(x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1,
                                                 x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0,
                                                 smooth=True, fill=col("lat_sel"), outline="")
                        cinta.create_image(x + ancho_ / 2, h // 2, image=icono_cinta(ico_, color_),
                                           tags=("item", "b:" + id_))
                        cinta.create_rectangle(x + 3, 6, x + ancho_ - 3, h - 6, outline="", fill="",
                                               tags=("item", "b:" + id_))
                        if id_ == "guardar" and n_resaltes():  # puntito: hay cambios sin guardar
                            cinta.create_oval(x + ancho_ - px(13), px(8), x + ancho_ - px(5), px(16), fill="#F97316",
                                              outline="")
                        app["cinta_acc"][id_] = acc_
                        app["cinta_ayuda"][id_] = ayuda_
                    x += ancho_
            return x

        poner(izq, 10)
        ancho_c = sum(sum(_ancho_item(i_) for i_ in g) for g in centro) + 10 * (len(centro) - 1)
        x_c = max(210, (w - ancho_c) // 2)
        poner(centro, x_c)
        ancho_d = sum(_ancho_item(i_) for i_ in der[0])
        poner(der, w - ancho_d - 10)

    # ayuda al pasar el mouse (los iconos no tienen texto)
    # v3.2.1: etiqueta comun de tk (las de CustomTkinter multiplican la posicion por la escala de Windows y,
    # con la pantalla al 125 % o 150 %, la ayuda del riel derecho quedaba fuera de la ventana)
    ayuda_lbl = tk.Label(raiz, text="", font=(FAM, 9), padx=8, pady=3, bd=0)
    ayuda_job = {"id": None, "tag": None}

    def ayuda_esconder(*_):
        if ayuda_job["id"]:
            raiz.after_cancel(ayuda_job["id"])
        ayuda_job.update(id=None, tag=None)
        ayuda_lbl.place_forget()

    def ayuda_mover(ev, canvas_, textos_):
        tag_ = None
        for it in reversed(canvas_.find_overlapping(ev.x, ev.y, ev.x, ev.y)):
            for t in canvas_.gettags(it):
                if t.startswith(("b:", "r:")):
                    tag_ = t
                    break
            if tag_:
                break
        if tag_ == ayuda_job["tag"]:
            return
        ayuda_esconder()
        texto_ = textos_().get(tag_[2:]) if tag_ else None
        if not texto_:
            return
        ayuda_job["tag"] = tag_
        x_ = canvas_.winfo_rootx() - raiz.winfo_rootx() + ev.x
        y_ = canvas_.winfo_rooty() - raiz.winfo_rooty() + ev.y + 22

        def mostrar_():
            ayuda_lbl.configure(text=texto_, bg=col("texto"), fg=col("tarjeta"))
            ayuda_lbl.update_idletasks()
            ancho_a = ayuda_lbl.winfo_reqwidth()
            if canvas_ is riel_der:  # a la izquierda del icono, a su altura
                xa, ya = canvas_.winfo_rootx() - raiz.winfo_rootx() - ancho_a - 6, y_ - 34
            else:
                xa, ya = min(x_ - 12, raiz.winfo_width() - ancho_a - 8), y_
            ayuda_lbl.place(x=max(4, xa), y=ya)
            ayuda_lbl.lift()
        ayuda_job["id"] = raiz.after(450, mostrar_)

    def click_cinta(ev):
        ayuda_esconder()
        for it in reversed(cinta.find_overlapping(ev.x, ev.y, ev.x, ev.y)):
            for t in cinta.gettags(it):
                if t.startswith("b:"):
                    acc_ = app.get("cinta_acc", {}).get(t[2:])
                    if acc_:
                        if app["vista_top"] and t[2:] not in ("abrir", "zoom_menu"):
                            app["vista_top"] = None
                            mostrar_inicio()
                            dibujar_superior()
                        acc_()
                    raiz.after(20, dibujar_cinta)
                    return

    cinta.bind("<Configure>", dibujar_cinta)
    cinta.bind("<Button-1>", click_cinta)
    cinta.bind("<Motion>", lambda e: ayuda_mover(e, cinta, lambda: app.get("cinta_ayuda", {})))
    cinta.bind("<Leave>", ayuda_esconder)
    dibujar_lateral = dibujar_superior  # nombre de la v1.1 (lo llaman perfiles y apariencia)

    # ---- franja de actualizacion (fila 1, solo cuando hay una version nueva)
    franja = ctk.CTkFrame(raiz, fg_color=("#E3EDFB", "#22324A"), corner_radius=0, height=42)
    franja.grid_columnconfigure(0, weight=1)
    v_franja = tk.StringVar(value="")
    ctk.CTkLabel(franja, textvariable=v_franja, font=F(13, "bold"), text_color=C["texto"], anchor="w").grid(
        row=0, column=0, sticky="ew", padx=(22, 10), pady=6)
    caja_franja = ctk.CTkFrame(franja, fg_color="transparent")
    caja_franja.grid(row=0, column=1, sticky="e", padx=(0, 18), pady=5)

    # ---- cuerpo: columna izquierda (miniaturas + tarjeta «Proceso») y el contenido
    # (opcion D: sin barra abajo, asi la hoja se ve completa)
    ANCHO_IZQ = 216
    cuerpo = ctk.CTkFrame(raiz, fg_color=C["fondo"], corner_radius=0)
    cuerpo.grid(row=3, column=0, sticky="nsew")
    cuerpo.grid_columnconfigure(2, weight=1)
    cuerpo.grid_rowconfigure(0, weight=1)
    # v3.0: riel de iconos a la izquierda (como Adobe): miniaturas, marcadores y buscar
    if not almacen.datos.get("v32_minis"):  # v3.2: como Adobe, las miniaturas empiezan cerradas (una vez)
        almacen.datos["v32_minis"] = True
        almacen.datos["miniaturas"] = False
    riel = ctk.CTkFrame(cuerpo, fg_color=C["tarjeta"], corner_radius=0, width=40)
    riel.grid(row=0, column=0, sticky="nsw")
    riel_b = {}
    col_izq = ctk.CTkFrame(cuerpo, fg_color="transparent", width=ANCHO_IZQ)
    col_izq.grid(row=0, column=1, sticky="nsw", padx=(10, 0), pady=(10, 12))
    col_izq.grid_propagate(False)
    col_izq.grid_columnconfigure(0, weight=1)
    col_izq.grid_rowconfigure(1, weight=1)
    # tarjeta del documento activo (en las pantallas que no son el visor)
    tarj_doc = ctk.CTkFrame(col_izq, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
    v_doc_nom = tk.StringVar(value="")
    ctk.CTkLabel(tarj_doc, text="Documento activo", font=F(13, "bold"), text_color=C["texto"], anchor="w").pack(
        fill="x", padx=14, pady=(12, 2))
    ctk.CTkLabel(tarj_doc, textvariable=v_doc_nom, font=F(12), text_color=C["acento"], anchor="w", justify="left",
                 wraplength=ANCHO_IZQ - 30).pack(fill="x", padx=14)
    ctk.CTkLabel(tarj_doc, textvariable=v_info_doc, font=F(11), text_color=C["texto2"], anchor="w", justify="left",
                 wraplength=ANCHO_IZQ - 30).pack(fill="x", padx=14, pady=(2, 12))
    # en Organizar: la lista de archivos unidos (con su color) y los atajos, aca al costado
    caja_org_izq = ctk.CTkFrame(tarj_doc, fg_color="transparent")
    l_archivos_tit = ctk.CTkLabel(caja_org_izq, text="Archivos", font=F(12, "bold"), text_color=C["texto"], anchor="w")
    # v3.0: la lista de archivos tiene su propio desplazamiento (con muchos PDF, «Procesar» quedaba fuera)
    leyenda = ctk.CTkScrollableFrame(caja_org_izq, fg_color="transparent", height=60,
                                     scrollbar_button_color=C["suave_h"], scrollbar_button_hover_color=C["borde"])

    contenido = ctk.CTkFrame(cuerpo, fg_color=C["fondo"], corner_radius=0)
    contenido.grid(row=0, column=2, sticky="nsew")
    contenido.grid_columnconfigure(0, weight=1)
    contenido.grid_rowconfigure(1, weight=1)
    titulo = ctk.CTkLabel(contenido, text="", font=F(28, "bold"), text_color=C["texto"], anchor="w")
    titulo.grid(row=0, column=0, sticky="ew", padx=36, pady=(20, 6))
    paginas = {}

    # ---- visor (se completa mas abajo) con el panel de la herramienta a la derecha
    visor = ctk.CTkFrame(contenido, fg_color=C["fondo"], corner_radius=0)
    paginas["visor"] = visor
    ANCHO_PANEL = 470
    # v3.2.2: el panel derecho vive al costado de todo (no solo del visor): Foliar, Aplanar y Comprimir se
    # ajustan tambien desde Organizar, que es donde se da «Procesar»
    panel_der = ctk.CTkFrame(cuerpo, fg_color=C["fondo"], corner_radius=12, border_width=1,
                             border_color=C["borde"], width=ANCHO_PANEL)
    panel_der.grid_propagate(False)
    panel_der.pack_propagate(False)
    panel_cab = ctk.CTkFrame(panel_der, fg_color="transparent")
    panel_cab.pack(fill="x", padx=(18, 8), pady=(10, 2))
    v_panel_tit = tk.StringVar(value="")
    l_panel_ico = ctk.CTkLabel(panel_cab, text="", width=28)
    l_panel_ico.pack(side="left", padx=(0, 8))
    ctk.CTkLabel(panel_cab, textvariable=v_panel_tit, font=F(18, "bold"), text_color=C["texto"]).pack(side="left")
    b_panel_x = ctk.CTkButton(panel_cab, text="✕", width=32, height=32, corner_radius=16, font=F(14),
                              fg_color="transparent", hover_color=C["suave_h"], text_color=C["texto2"],
                              command=lambda: cerrar_panel())
    b_panel_x.pack(side="right")
    paneles = {}           # aplanar / foliar / comprimir: se muestran en el panel derecho
    PAGINAS_PANEL = set()

    # ---- tarjeta «Proceso» (lo que era la barra de abajo): debajo de las miniaturas
    inferior = ctk.CTkFrame(col_izq, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
    inferior.grid(row=2, column=0, sticky="sew", pady=(8, 0))
    inferior.grid_columnconfigure(0, weight=1)
    ctk.CTkLabel(inferior, text="Proceso", font=F(13, "bold"), text_color=C["texto"], anchor="w").grid(
        row=0, column=0, sticky="ew", padx=14, pady=(10, 6))
    # v3.2.2: en Organizar, que hacer al procesar (y sus ajustes) a la vista, junto a «Procesar»
    caja_opc_org = ctk.CTkFrame(inferior, fg_color="transparent")
    ctk.CTkLabel(caja_opc_org, text="Al procesar también:", font=F(11), text_color=C["texto2"], anchor="w").pack(
        fill="x", padx=4, pady=(0, 4))
    fila_opc_org = ctk.CTkFrame(caja_opc_org, fg_color="transparent")
    fila_opc_org.pack(fill="x")
    chips_org = {}
    for k_o, (cl_o, txt_o) in enumerate((("fol", "Foliar"), ("apl", "Aplanar"), ("comp", "Comprimir"))):
        chips_org[cl_o] = ctk.CTkButton(fila_opc_org, text=txt_o, height=28, corner_radius=8, font=F(12),
                                        anchor="w", fg_color=C["suave"], hover_color=C["suave_h"],
                                        text_color=C["texto"])
        chips_org[cl_o].pack(fill="x", padx=2, pady=2)
    ctk.CTkLabel(caja_opc_org, text="Tocá una para activarla y ver sus ajustes a la derecha.", font=F(10),
                 text_color=C["texto2"], anchor="w", wraplength=ANCHO_IZQ - 34, justify="left").pack(
        fill="x", padx=4, pady=(4, 6))
    caja_bot = ctk.CTkFrame(inferior, fg_color="transparent")
    caja_bot.grid(row=2, column=0, sticky="ew", padx=10)
    caja_bot.grid_columnconfigure((0, 1), weight=1, uniform="bp")
    caja_estado = ctk.CTkFrame(inferior, fg_color="transparent")
    caja_estado.grid(row=3, column=0, sticky="ew", padx=12, pady=(8, 12))
    caja_estado.grid_columnconfigure(0, weight=1)
    barra = ctk.CTkProgressBar(caja_estado, height=6, progress_color=C["acento"], fg_color=C["suave"])
    barra.grid(row=0, column=0, sticky="ew", pady=(0, 6))
    barra.set(0)
    ctk.CTkLabel(caja_estado, textvariable=v_estado, font=F(12, "bold"), text_color=C["texto"], anchor="w",
                 justify="left", wraplength=ANCHO_IZQ - 34).grid(row=1, column=0, sticky="ew")
    lbl_det = ctk.CTkLabel(caja_estado, textvariable=v_detalle, font=F(10), text_color=C["texto2"], anchor="w",
                           justify="left", wraplength=ANCHO_IZQ - 34)
    lbl_det.grid(row=2, column=0, sticky="ew", pady=(2, 0))

    def boton(master, texto, primario=False, ancho=110, **kw):
        if primario:
            return ctk.CTkButton(master, text=texto, width=ancho, height=34, corner_radius=8, font=F(13, "bold"),
                                 fg_color=C["acento"], hover_color=C["acento_h"], text_color="#FFFFFF",
                                 text_color_disabled=("#C9D5E4", "#9FB2CC"), **kw)
        return ctk.CTkButton(master, text=texto, width=ancho, height=34, corner_radius=8, font=F(13),
                             fg_color=C["suave"], hover_color=C["suave_h"], text_color=C["texto"],
                             text_color_disabled=C["texto2"], **kw)

    b_analizar = boton(caja_bot, "Analizar", ancho=90)
    b_procesar = boton(caja_bot, "Procesar", primario=True, ancho=90)
    b_cancelar = boton(caja_bot, "Cancelar", ancho=90)
    b_carpeta = boton(caja_bot, "Abrir carpeta", ancho=90)
    for k, b in enumerate((b_analizar, b_procesar, b_cancelar, b_carpeta)):
        b.configure(height=30, font=F(12 if b is not b_carpeta else 11, "bold" if b is b_procesar else "normal"))
        b.grid(row=k // 2, column=k % 2, padx=3, pady=3, sticky="ew")

    # ================================================== COMPONENTES
    def pagina_nueva(clave):
        en_panel = clave in EN_PANEL
        p = ctk.CTkScrollableFrame(panel_der if en_panel else contenido, fg_color=C["fondo"], corner_radius=0,
                                   scrollbar_button_color=C["suave_h"], scrollbar_button_hover_color=C["borde"])
        p.grid_columnconfigure(0, weight=1)
        if en_panel:
            paneles[clave] = p
            PAGINAS_PANEL.add(p)
        else:
            paginas[clave] = p
        return p

    def seccion(master, texto, fila, col=0, pady=(18, 8)):
        px_ = (14, 14) if master in PAGINAS_PANEL else (36, 36)
        ctk.CTkLabel(master, text=texto, font=F(16, "bold"), text_color=C["texto"], anchor="w").grid(
            row=fila, column=col, sticky="ew", padx=px_, pady=pady)

    # v4.0: barra de desplazamiento DIBUJADA (una raya redondeada). La de customtkinter se redibujaba entera en
    # cada paso de la rueda: era parte de lo que hacia lento el desplazamiento
    def _color_fondo(w_):
        while w_ is not None:
            try:
                c_ = w_.cget("fg_color")
            except Exception:
                try:
                    return w_.cget("bg")
                except Exception:
                    return col("fondo")
            if c_ != "transparent":
                return c_[1 if modo_oscuro() else 0] if isinstance(c_, (tuple, list)) else c_
            w_ = w_.master
        return col("fondo")

    class Desliz(tk.Canvas):
        todas = []

        def __init__(self, master, command=None, orientation="vertical", button_color=None,
                     button_hover_color=None, **_kw):
            Desliz.todas.append(self)
            self.vert = orientation != "horizontal"
            g_ = px(12)
            super().__init__(master, highlightthickness=0, bd=0, **({"width": g_} if self.vert else {"height": g_}))
            self.cmd = command
            self.c_n = button_color or C["suave_h"]
            self.c_h = button_hover_color or C["borde"]
            self.lo, self.hi = 0.0, 1.0
            self._arr = None
            self._sobre = False
            self.raya = self.create_line(0, 0, 0, 0, width=px(8), capstyle="round")
            self.bind("<Configure>", lambda e: self._pintar(True))
            self.bind("<ButtonPress-1>", self._press)
            self.bind("<B1-Motion>", self._mover)
            self.bind("<ButtonRelease-1>", lambda e: setattr(self, "_arr", None))
            self.bind("<Enter>", lambda e: (setattr(self, "_sobre", True), self._pintar(True)))
            self.bind("<Leave>", lambda e: (setattr(self, "_sobre", False), self._pintar(True)))
            self._tema = None

        def configure(self, cnf=None, **kw):
            if "command" in kw:
                self.cmd = kw.pop("command")
            if "button_color" in kw:
                self.c_n = kw.pop("button_color")
            if "button_hover_color" in kw:
                self.c_h = kw.pop("button_hover_color")
            kw.pop("fg_color", None)
            if cnf or kw:
                return super().configure(cnf, **kw)
            self._pintar(True)
        config = configure

        def _largo(self):
            return max(1, self.winfo_height() if self.vert else self.winfo_width())

        def _pintar(self, colores=False):
            L, g_ = self._largo(), px(12)
            m_ = px(6)
            pista = max(1, L - 2 * m_)
            minimo = px(28)  # largo minimo de la raya (para poder tomarla)
            real = (self.hi - self.lo) * pista
            extra = max(0.0, minimo - real)
            a_ = m_ + self.lo * (pista - extra)
            b_ = a_ + real + extra
            self._ab = (a_, b_, pista - extra)
            lleno = self.lo <= 0.0 and self.hi >= 1.0
            if self.vert:
                self.coords(self.raya, g_ / 2, a_, g_ / 2, b_)
            else:
                self.coords(self.raya, a_, g_ / 2, b_, g_ / 2)
            tema = (modo_oscuro(), self._sobre, lleno)
            if colores or tema != self._tema:
                self._tema = tema
                c_ = self.c_h if self._sobre else self.c_n
                c_ = c_[1 if modo_oscuro() else 0] if isinstance(c_, (tuple, list)) else c_
                super().configure(bg=_color_fondo(self.master))
                self.itemconfigure(self.raya, fill=c_, state="hidden" if lleno else "normal")

        def set(self, lo, hi):
            lo, hi = float(lo), float(hi)
            if (lo, hi) != (self.lo, self.hi):
                self.lo, self.hi = lo, hi
                self._pintar()

        def get(self):
            return self.lo, self.hi

        def reescalar(self):
            tk.Canvas.configure(self, **({"width": px(12)} if self.vert else {"height": px(12)}))
            self.itemconfigure(self.raya, width=px(8))
            self._pintar(True)

        def _press(self, ev):
            # v4.0.1: se toma la raya por donde se VE (antes se calculaba sin el largo minimo y casi nunca se
            # podia agarrar en documentos largos)
            pos = ev.y if self.vert else ev.x
            a_, b_, util = getattr(self, "_ab", (0, 0, 1))
            if a_ - px(4) <= pos <= b_ + px(4):
                self._arr = (pos, self.lo, max(1.0, util))
            elif self.cmd:
                self.cmd("scroll", -1 if pos < a_ else 1, "pages")

        def _mover(self, ev):
            if self._arr and self.cmd:
                p0, lo0, util = self._arr
                pos = ev.y if self.vert else ev.x
                self.cmd("moveto", max(0.0, min(1.0, lo0 + (pos - p0) / util)))

    class Tarjeta(ctk.CTkFrame):
        def __init__(self, master, fila, col=0, colspan=1, padx=(36, 36)):
            self._wrap = 330
            if master in PAGINAS_PANEL:  # en el panel derecho: mas angosta
                padx, self._wrap = (12, 12), 190
            super().__init__(master, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
            self.grid(row=fila, column=col, columnspan=colspan, sticky="new", padx=padx, pady=(0, 6))
            self.grid_columnconfigure(1, weight=1)
            self._n = 0

        def fila(self, etiqueta, widget=None, ayuda=None, abajo=False):
            if self._n:
                ctk.CTkFrame(self, height=1, fg_color=C["linea"], corner_radius=0).grid(
                    row=self._n * 2 - 1, column=0, columnspan=2, sticky="ew", padx=16)
            r = self._n * 2
            caja = ctk.CTkFrame(self, fg_color="transparent")
            caja.grid(row=r, column=0, columnspan=2 if abajo else 1, sticky="w", padx=(18, 10), pady=11)
            ctk.CTkLabel(caja, text=etiqueta, font=F(13), text_color=C["texto"], anchor="w").pack(anchor="w")
            if ayuda:
                ctk.CTkLabel(caja, text=ayuda, font=F(11), text_color=C["texto2"], anchor="w",
                             justify="left", wraplength=self._wrap).pack(anchor="w")
            if widget is not None:
                if abajo:  # control en su propia linea, debajo de la etiqueta
                    widget.pack(in_=caja, anchor="w", pady=(8, 0))
                    widget.lift(caja)
                else:
                    widget.grid(row=r, column=1, sticky="e", padx=(10, 16), pady=9)
            self._n += 1
            return caja

    imgs_sw = {}
    for enc in (True, False):
        for act_ in (True, False):
            imgs_sw[(enc, act_)] = ctk.CTkImage(light_image=_img_interruptor(enc, False, act_),
                                                dark_image=_img_interruptor(enc, True, act_), size=(44, 24))

    class Interruptor(ctk.CTkLabel):
        """Interruptor propio (imagen nitida en claro/oscuro), ligado a un BooleanVar."""

        def __init__(self, master, var):
            super().__init__(master, text="", width=44, height=24, cursor="hand2")
            self.var, self.activo = var, True
            self.bind("<Button-1>", self._clic)
            var.trace_add("write", lambda *_: self._pintar())
            self._pintar()

        def _clic(self, _=None):
            if self.activo:
                self.var.set(not self.var.get())

        def _pintar(self):
            super().configure(image=imgs_sw[(bool(self.var.get()), self.activo)])

        def configure(self, **kw):
            if "state" in kw:
                self.activo = kw.pop("state") != "disabled"
                super().configure(cursor="hand2" if self.activo else "arrow")
                self._pintar()
            if kw:
                super().configure(**kw)

    def switch(master, var, cmd=None):
        return Interruptor(master, var)

    def segmentado(master, valores, var, ancho=None, cmd=None):
        s = ctk.CTkSegmentedButton(master, values=valores, variable=var, font=F(12), height=30,
                                   selected_color=C["acento"], selected_hover_color=C["acento_h"],
                                   unselected_color=C["suave"], unselected_hover_color=C["suave_h"],
                                   fg_color=C["suave"], text_color=(C["texto"][0], C["texto"][1]),
                                   corner_radius=8, command=cmd)
        if ancho:
            s.configure(width=ancho)
        return s

    def menu(master, valores, var, ancho=200, cmd=None):
        return ctk.CTkOptionMenu(master, values=valores, variable=var, width=ancho, height=30, corner_radius=8,
                                 font=F(12), dropdown_font=F(12), fg_color=C["suave"], button_color=C["suave_h"],
                                 button_hover_color=C["borde"], text_color=C["texto"],
                                 dropdown_fg_color=C["tarjeta"], dropdown_hover_color=C["suave"],
                                 dropdown_text_color=C["texto"], command=cmd, dynamic_resizing=False)

    def entrada(master, var, ancho=160, **kw):
        return ctk.CTkEntry(master, textvariable=var, width=ancho, height=30, corner_radius=8, font=F(12),
                            fg_color=C["campo"], border_color=C["borde"], text_color=C["texto"], **kw)

    class Contador(ctk.CTkFrame):
        """Campo numerico con botones − / + (permite vacio si 'vacio=True')."""

        def __init__(self, master, var, minimo, maximo, paso=1, ancho=70, vacio=False, decimales=False):
            super().__init__(master, fg_color=C["suave"], corner_radius=8, height=30)
            self.var, self.minimo, self.maximo, self.paso = var, minimo, maximo, paso
            self.vacio, self.dec = vacio, decimales
            self.b1 = ctk.CTkButton(self, text="−", width=28, height=28, corner_radius=7, font=F(14),
                                    fg_color="transparent", hover_color=C["suave_h"], text_color=C["texto"],
                                    command=lambda: self.mover(-1))
            self.e = ctk.CTkEntry(self, textvariable=var, width=ancho, height=28, corner_radius=6, font=F(12),
                                  justify="center", fg_color=C["campo"], border_width=0, text_color=C["texto"])
            self.b2 = ctk.CTkButton(self, text="+", width=28, height=28, corner_radius=7, font=F(14),
                                    fg_color="transparent", hover_color=C["suave_h"], text_color=C["texto"],
                                    command=lambda: self.mover(1))
            self.b1.pack(side="left", padx=(1, 0), pady=1)
            self.e.pack(side="left", pady=1)
            self.b2.pack(side="left", padx=(0, 1), pady=1)

        def mover(self, d):
            t = self.var.get().strip().replace(",", ".")
            try:
                v = float(t) if t else (self.minimo if d > 0 else self.minimo)
            except ValueError:
                v = self.minimo
            if not t and self.vacio:
                v = self.minimo
            else:
                v += d * self.paso
            v = max(self.minimo, min(self.maximo, v))
            self.var.set((f"{v:g}") if self.dec else str(int(round(v))))

        def configure(self, **kw):
            if "state" in kw:
                st = kw.pop("state")
                for w in (self.b1, self.e, self.b2):
                    w.configure(state=st)
            if kw:
                super().configure(**kw)

    # v2.5: las paginas que no se ven al abrir se arman despues (la ventana aparece antes)
    por_armar = {}
    b_buscar = sw_apl = sw_comp = b_pdf_def = b_buscar_act = b_reiniciar_tema = None
    ctrl_apl, ctrl_comp, filas_perfil = [], [], []
    botones_tema, botones_color_tema = {}, {}
    v_ayuda_niv = tk.StringVar(value=AYUDA_NIVEL[V["nivel"].get()])
    tema_actual = almacen.datos.get("tema", "Azul gris")
    v_aviso_tema = tk.StringVar(value="Cada color tiene su versión clara y oscura (según el Modo de arriba).")

    def asegurar_pagina(clave):
        f_ = por_armar.pop(clave, None)
        if f_ is not None:
            f_()
            try:
                refrescar()
            except Exception:
                pass

    def armar_lo_que_falta():
        """Despues de mostrar la ventana: una pagina por vez, sin trabar."""
        if por_armar:
            asegurar_pagina(next(iter(por_armar)))
            raiz.after(120, armar_lo_que_falta)

    # ================================================== PAGINA: DOCUMENTO
    def _armar_documento():
        nonlocal b_buscar
        p = pagina_nueva("documento")
        seccion(p, "Archivo PDF", 0, pady=(6, 8))
        t = Tarjeta(p, 1)
        fila_archivo = ctk.CTkFrame(t, fg_color="transparent")
        fila_archivo.grid(row=0, column=0, columnspan=2, sticky="ew", padx=16, pady=14)
        fila_archivo.grid_columnconfigure(0, weight=1)
        e_ruta = entrada(fila_archivo, V["ruta"], ancho=400, state="readonly")
        e_ruta.grid(row=0, column=0, sticky="ew", padx=(0, 10))
        b_buscar = boton(fila_archivo, "Buscar…", primario=True, ancho=110)
        b_buscar.grid(row=0, column=1)
        ctk.CTkLabel(t, textvariable=v_info_doc, font=F(12), text_color=C["texto2"], anchor="w").grid(
            row=1, column=0, columnspan=2, sticky="ew", padx=18, pady=(0, 4))
        ctk.CTkLabel(t, text="Es el documento de la pestaña activa. «Buscar…» lo abre en una pestaña nueva.",
                     font=F(11), text_color=C["texto2"], anchor="w").grid(
            row=2, column=0, columnspan=2, sticky="ew", padx=18, pady=(0, 14))
        seccion(p, "Qué hacer", 2)
        t = Tarjeta(p, 3)
        t.fila("Aplanar planos pesados", switch(t, V["apl"]),
               "Convierte en imagen de alta resolución solo los planos lentos.")
        t.fila("Foliar páginas", switch(t, V["fol"]), "Agrega el número de folio con el estilo que elijas.")
        t.fila("Comprimir", switch(t, V["comp"]), "Reduce el tamaño sin bajar la resolución.")
        ctk.CTkLabel(p, text="Orden de proceso: aplanar → foliar → comprimir.  El original nunca se modifica.",
                     font=F(11), text_color=C["texto2"], anchor="w").grid(row=4, column=0, sticky="ew", padx=40, pady=(4, 20))
        b_buscar.configure(command=buscar)
    por_armar["documento"] = _armar_documento

    # ================================================== PAGINA: APLANAR
    def _armar_aplanar():
        nonlocal sw_apl, ctrl_apl
        p = pagina_nueva("aplanar")
        t = Tarjeta(p, 0)
        sw_apl = switch(t, V["apl"])
        t.fila("Aplanar planos pesados", sw_apl, "Los planos con muchos vectores se convierten en imagen para que carguen rápido.")
        seccion(p, "Calidad", 1)
        t = Tarjeta(p, 2)
        seg_dpi = segmentado(t, ["200", "300", "400", "500"], V["dpi"], ancho=260)
        t.fila("Resolución (dpi)", seg_dpi, "400 es el punto ideal entre nitidez y peso.")
        sw_txt = switch(t, V["texto"])
        t.fila("Conservar texto buscable", sw_txt, "Permite seguir buscando en los planos con Ctrl+F.")
        m_nuc = menu(t, ["Automático"] + [str(k) for k in range(1, (os.cpu_count() or 2) + 1)], V["nucleos"], 150)
        t.fila("Núcleos del procesador", m_nuc, f"Esta PC tiene {os.cpu_count() or 1}. Automático deja uno libre.")
        seccion(p, "Páginas", 3)
        t = Tarjeta(p, 4)
        e_extra = entrada(t, V["extra"], 200)
        t.fila("Agregar páginas", e_extra, "Además de las detectadas. Ej.: 15, 20-35")
        e_excl = entrada(t, V["excluir"], 200)
        t.fila("Excluir páginas", e_excl, "Nunca se aplanan. Ej.: 1-3")
        ctk.CTkLabel(p, textvariable=v_info_apl, font=F(12), text_color=C["texto2"], anchor="w", justify="left",
                     wraplength=440).grid(row=5, column=0, sticky="ew", padx=18, pady=(8, 20))
        ctrl_apl = [seg_dpi, sw_txt, m_nuc, e_extra, e_excl]
    por_armar["aplanar"] = _armar_aplanar

    # ================================================== PAGINA: FOLIAR
    V["girar_prev"] = tk.BooleanVar(value=False)
    sw_fol = e_pref = b_otro = lbl_mini = lbl_zoom = None
    puntos_color, botones_pos, ctrl_fol = [], {}, []

    def _armar_foliar():
        nonlocal sw_fol, e_pref, b_otro, lbl_mini, lbl_zoom, puntos_color, botones_pos, ctrl_fol
        p = pagina_nueva("foliar")
        p.grid_columnconfigure(0, weight=1)
        p.grid_columnconfigure(1, weight=0)
        t = Tarjeta(p, 0, padx=(36, 12))
        sw_fol = switch(t, V["fol"])
        t.fila("Foliar páginas", sw_fol, "Número de folio como texto nítido (también en planos aplanados).")
        seccion(p, "Numeración", 1)
        t = Tarjeta(p, 2, padx=(36, 12))
        c_inicio = Contador(t, V["inicio"], 0, 99999999, ancho=90)
        t.fila("Iniciar en", c_inicio, "Desde 0 en adelante.")
        c_dig = Contador(t, V["digitos"], 1, 10, ancho=50)
        t.fila("Dígitos", c_dig, "Total de dígitos: con 4, el 1 sale como 0001.")
        c_desde = Contador(t, V["desde"], 1, 999999, ancho=70)
        t.fila("Desde la página", c_desde)
        c_hasta = Contador(t, V["hasta"], 1, 999999, ancho=70, vacio=True)
        t.fila("Hasta la página", c_hasta, "Vacío = hasta el final.")
        seg_fmt = segmentado(t, ["Solo número", "Número / total"], V["formato"], ancho=250)
        t.fila("Formato", seg_fmt)
        caja_pref = ctk.CTkFrame(t, fg_color="transparent")
        seg_pref = segmentado(caja_pref, ["Sin texto", "Pág.", "Folio", "Escribir"], V["prefijo"], ancho=280)
        seg_pref.pack(anchor="e")
        e_pref = entrada(caja_pref, V["prefijo_txt"], 280)
        e_pref.pack(anchor="e", pady=(6, 0))
        t.fila("Texto antes del número", caja_pref)

        seccion(p, "Estilo", 3)
        t = Tarjeta(p, 4, padx=(36, 12))
        m_fuente = menu(t, fuentes, V["fuente"], 230)
        t.fila("Fuente", m_fuente, "Las primeras 8 son estilo foliador / sello y vienen incluidas.")
        c_tam = Contador(t, V["tam"], 4, 96, ancho=50, decimales=True)
        t.fila("Tamaño en papel (pt)", c_tam, "Mide lo mismo en todas las hojas impresas (carta, o A3 los planos).")
        sw_neg = switch(t, V["negrita"])
        t.fila("Negrita", sw_neg)
        caja_col = ctk.CTkFrame(t, fg_color="transparent")
        puntos_color = []
        for nombre_c, rgb in COLORES_FOLIO:
            hx = "#%02x%02x%02x" % rgb
            b = ctk.CTkButton(caja_col, text="", width=22, height=22, corner_radius=11, fg_color=hx, hover_color=hx,
                              border_width=0, border_color=C["acento"])
            b.pack(side="left", padx=3)
            puntos_color.append((b, rgb))
        b_otro = ctk.CTkButton(caja_col, text="Otro…", width=58, height=24, corner_radius=12, font=F(11),
                               fg_color=C["suave"], hover_color=C["suave_h"], text_color=C["texto"])
        b_otro.pack(side="left", padx=(8, 0))
        t.fila("Color", caja_col, abajo=True)

        seccion(p, "Posición", 5)
        t = Tarjeta(p, 6, padx=(36, 12))
        # selector visual de posicion (hoja con 6 puntos)
        caja_hoja = ctk.CTkFrame(t, fg_color="transparent")
        hoja = ctk.CTkFrame(caja_hoja, width=104, height=134, fg_color=C["campo"], corner_radius=8,
                            border_width=1, border_color=C["borde"])
        hoja.grid_propagate(False)
        botones_pos = {}
        lugares = {"Arriba izquierda": (0.17, 0.12), "Arriba centro": (0.5, 0.12), "Arriba derecha": (0.83, 0.12),
                   "Abajo izquierda": (0.17, 0.88), "Abajo centro": (0.5, 0.88), "Abajo derecha": (0.83, 0.88)}
        for nombre_p, (rx, ry) in lugares.items():
            b = ctk.CTkButton(hoja, text="", width=18, height=18, corner_radius=9, fg_color=C["suave_h"],
                              hover_color=C["acento_h"], border_width=0,
                              command=lambda n_=nombre_p: V["pos"].set(n_))
            b.place(relx=rx, rely=ry, anchor="center")
            botones_pos[nombre_p] = b
        for k in range(4):  # lineas de "texto" decorativas
            ctk.CTkFrame(hoja, width=60 - (k % 2) * 16, height=4, fg_color=C["suave"], corner_radius=2).place(
                relx=0.5, rely=0.32 + k * 0.1, anchor="center")
        hoja.pack(side="right")
        ctk.CTkLabel(caja_hoja, textvariable=V["pos"], font=F(12, "bold"), text_color=C["acento"]).pack(
            side="right", padx=(0, 14))
        t.fila("Ubicación en la página", caja_hoja, "Tocá uno de los puntos de la hoja.")
        c_mh = Contador(t, V["mh"], -300, 300, ancho=56, decimales=True)
        t.fila("Margen horizontal (mm)", c_mh, "En el papel, con la hoja parada. Centrado: + derecha / − izquierda.")
        c_mv = Contador(t, V["mv"], 0, 300, ancho=56, decimales=True)
        t.fila("Margen vertical (mm)", c_mv, "En el papel, con la hoja parada.")
        ctk.CTkLabel(p, text="La vista previa está abajo. El folio también se ve en vivo sobre el documento.",
                     font=F(11), text_color=C["texto2"], anchor="w", justify="left", wraplength=440).grid(
            row=7, column=0, sticky="ew", padx=18, pady=(10, 0))

        # vista previa (columna derecha)
        prev_card = ctk.CTkFrame(p, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
        prev_card.grid(row=8, column=0, sticky="new", padx=(12, 12), pady=(14, 16))
        ctk.CTkLabel(prev_card, text="Vista previa", font=F(14, "bold"), text_color=C["texto"], anchor="w").pack(
            anchor="w", padx=16, pady=(14, 2))
        ctk.CTkLabel(prev_card, textvariable=v_ejemplo, font=F(13, "bold"), text_color=C["acento"], anchor="w").pack(
            anchor="w", padx=16, pady=(0, 10))
        ctk.CTkCheckBox(prev_card, text="Ver como hoja impresa (horizontales paradas)", variable=V["girar_prev"],
                        font=F(11), text_color=C["texto"], fg_color=C["acento"], hover_color=C["acento_h"],
                        border_color=C["texto2"], checkbox_width=18, checkbox_height=18, border_width=2,
                        ).pack(anchor="w", padx=16, pady=(0, 8))
        lbl_mini = ctk.CTkLabel(prev_card, text="", width=250, height=330, fg_color=C["campo"], corner_radius=8)
        lbl_mini.pack(padx=16)
        ctk.CTkLabel(prev_card, text="Acercamiento", font=F(11), text_color=C["texto2"], anchor="w").pack(
            anchor="w", padx=16, pady=(10, 2))
        lbl_zoom = ctk.CTkLabel(prev_card, text="", width=250, height=110, fg_color=C["campo"], corner_radius=8)
        lbl_zoom.pack(padx=16)
        ctk.CTkLabel(prev_card, textvariable=v_prev_info, font=F(11), text_color=C["texto2"], anchor="w",
                     justify="left", wraplength=250).pack(anchor="w", padx=16, pady=(8, 14))
        ctrl_fol = [c_inicio, c_dig, c_desde, c_hasta, seg_fmt, seg_pref, m_fuente, c_tam, sw_neg, b_otro,
                    c_mh, c_mv] + [b for b, _ in puntos_color] + list(botones_pos.values())
        b_otro.configure(command=color_otro)
        for b, rgb in puntos_color:
            b.configure(command=lambda c_=rgb: poner_color(c_))
        poner_color(app.get("color") or (0, 0, 0), refrescar_prev=False)
        marcar_posicion()
    por_armar["foliar"] = _armar_foliar

    # ================================================== PAGINA: COMPRIMIR
    def _armar_comprimir():
        nonlocal sw_comp, ctrl_comp
        p = pagina_nueva("comprimir")
        t = Tarjeta(p, 0)
        sw_comp = switch(t, V["comp"])
        t.fila("Comprimir", sw_comp, "Nunca baja la resolución de las imágenes.")
        seccion(p, "Nivel", 1)
        t = Tarjeta(p, 2)
        seg_nivel = segmentado(t, list(NIVELES_UI), V["nivel"], ancho=290)
        caja_niv = t.fila("Nivel de compresión", seg_nivel)
        ctk.CTkLabel(t, textvariable=v_ayuda_niv, font=F(12), text_color=C["texto2"], anchor="w", justify="left",
                     wraplength=440).grid(row=1, column=0, columnspan=2, sticky="ew", padx=18, pady=(0, 14))
        ctk.CTkLabel(p, text="Los planos aplanados se guardan con compresión exacta cuando es más liviana,\n"
                             "así las líneas quedan perfectas.", font=F(11), text_color=C["texto2"], anchor="w",
                     justify="left").grid(row=3, column=0, sticky="ew", padx=18, pady=(10, 20))
        ctrl_comp = [seg_nivel]
    por_armar["comprimir"] = _armar_comprimir

    # ================================================== PAGINA: PERFILES
    def _armar_perfiles():
        nonlocal filas_perfil
        p = pagina_nueva("perfiles")
        ctk.CTkLabel(p, text="Guardá hasta 10 configuraciones completas (aplanar, foliar y comprimir). "
                             "Al abrir el programa se carga el último perfil usado.",
                     font=F(12), text_color=C["texto2"], anchor="w", justify="left", wraplength=700).grid(
            row=0, column=0, sticky="ew", padx=38, pady=(0, 10))
        t_perf = Tarjeta(p, 1)
        t_perf.grid_columnconfigure(0, weight=1)
        filas_perfil = []
        for k in range(MAX_PERFILES):
            if k:
                ctk.CTkFrame(t_perf, height=1, fg_color=C["linea"], corner_radius=0).grid(
                    row=k * 2 - 1, column=0, columnspan=2, sticky="ew", padx=16)
            izq_ = ctk.CTkFrame(t_perf, fg_color="transparent")
            izq_.grid(row=k * 2, column=0, sticky="w", padx=(16, 8), pady=8)
            num = ctk.CTkLabel(izq_, text=str(k + 1), width=28, height=28, corner_radius=14, font=F(12, "bold"),
                               fg_color=C["suave"], text_color=C["texto2"])
            num.pack(side="left")
            nom = ctk.CTkLabel(izq_, text="", font=F(13), text_color=C["texto"], anchor="w")
            nom.pack(side="left", padx=(12, 0))
            uso = ctk.CTkLabel(izq_, text="", font=F(11, "bold"), text_color=C["acento"])
            uso.pack(side="left", padx=(10, 0))
            der_ = ctk.CTkFrame(t_perf, fg_color="transparent")
            der_.grid(row=k * 2, column=1, sticky="e", padx=(8, 14), pady=8)
            bc = boton(der_, "Cargar", ancho=74)
            bg = boton(der_, "Guardar aquí", primario=True, ancho=104)
            br = boton(der_, "Renombrar", ancho=92)
            be = boton(der_, "Eliminar", ancho=78)
            for b in (bc, bg, br, be):
                b.configure(height=28, font=F(12))
                b.pack(side="left", padx=3)
            filas_perfil.append((num, nom, uso, bc, bg, br, be))
        ctk.CTkLabel(p, text=f"Los perfiles se guardan en: {almacen.ruta}", font=F(10), text_color=C["texto2"],
                     anchor="w", wraplength=700, justify="left").grid(row=2, column=0, sticky="ew", padx=40, pady=(8, 20))
        for i, (_, _, _, bc, bg, br, be) in enumerate(filas_perfil):
            bc.configure(command=lambda i=i: perfil_cargar(i))
            bg.configure(command=lambda i=i: perfil_guardar(i))
            br.configure(command=lambda i=i: perfil_renombrar(i))
            be.configure(command=lambda i=i: perfil_eliminar(i))
        refrescar_perfiles()
    por_armar["perfiles"] = _armar_perfiles

    # ================================================== PAGINA: APARIENCIA
    def _armar_apariencia():
        nonlocal b_pdf_def, botones_tema, b_buscar_act, botones_color_tema, b_reiniciar_tema
        p = pagina_nueva("apariencia")
        seccion(p, "Modo", 0, pady=(6, 8))
        t = Tarjeta(p, 1)
        caja_temas = ctk.CTkFrame(t, fg_color="transparent")
        caja_temas.grid(row=0, column=0, columnspan=2, sticky="w", padx=18, pady=16)
        botones_tema = {}
        for k, modo in enumerate(("Claro", "Oscuro", "Automático")):
            img = ctk.CTkImage(_miniatura_tema(modo), size=(96, 64))
            b = ctk.CTkButton(caja_temas, text="", image=img, width=108, height=74, corner_radius=10,
                              fg_color="transparent", hover_color=C["suave"], border_width=2,
                              border_color=C["tarjeta"], command=lambda m=modo: V["apariencia"].set(m))
            b.grid(row=0, column=k, padx=10)
            ctk.CTkLabel(caja_temas, text=modo, font=F(12), text_color=C["texto"]).grid(row=1, column=k, pady=(4, 0))
            botones_tema[modo] = b
        ctk.CTkLabel(t, text="Automático sigue el modo de Windows (claro u oscuro).", font=F(11),
                     text_color=C["texto2"], anchor="w").grid(row=1, column=0, columnspan=2, sticky="w", padx=20, pady=(0, 14))
        seccion(p, "Color del tema", 2)
        t = Tarjeta(p, 3)
        caja_col_tema = ctk.CTkFrame(t, fg_color="transparent")
        caja_col_tema.grid(row=0, column=0, columnspan=2, sticky="w", padx=18, pady=16)
        v_tema = tk.StringVar(value=tema_actual)
        botones_color_tema = {}

        def muestra_tema(nombre, oscuro_):
            pal = TEMAS[nombre]
            k_ = 1 if oscuro_ else 0
            W_, H_, E_ = 96, 64, 3
            im_ = Image.new("RGB", (W_ * E_, H_ * E_), _hex(pal["fondo"][k_]))
            d_ = ImageDraw.Draw(im_)
            d_.rectangle([0, 0, W_ * E_, 14 * E_], fill=_hex(pal["lat_fin"][k_]))
            d_.rounded_rectangle([6 * E_, 20 * E_, 30 * E_, 58 * E_], radius=4 * E_, fill=_hex(pal["tarjeta"][k_]))
            d_.rounded_rectangle([36 * E_, 20 * E_, 90 * E_, 58 * E_], radius=4 * E_, fill=_hex(pal["tarjeta"][k_]))
            d_.rounded_rectangle([42 * E_, 44 * E_, 70 * E_, 52 * E_], radius=3 * E_, fill=_hex(pal["acento"][k_]))
            d_.rounded_rectangle([42 * E_, 28 * E_, 84 * E_, 32 * E_], radius=2 * E_, fill=_hex(pal["suave"][k_]))
            d_.rounded_rectangle([0, 0, W_ * E_ - 1, H_ * E_ - 1], radius=6 * E_, outline=_hex(pal["borde"][k_]), width=E_)
            return im_.resize((W_, H_), Image.LANCZOS)

        for k, nombre in enumerate(TEMAS):
            img = ctk.CTkImage(light_image=muestra_tema(nombre, False), dark_image=muestra_tema(nombre, True),
                               size=(96, 64))
            b = ctk.CTkButton(caja_col_tema, text="", image=img, width=108, height=74, corner_radius=10,
                              fg_color="transparent", hover_color=C["suave"], border_width=2,
                              border_color=C["acento"] if nombre == tema_actual else C["tarjeta"],
                              command=lambda n_=nombre: elegir_tema(n_))
            b.grid(row=0, column=k, padx=10)
            ctk.CTkLabel(caja_col_tema, text=nombre, font=F(12), text_color=C["texto"]).grid(row=1, column=k, pady=(4, 0))
            botones_color_tema[nombre] = b
        ctk.CTkLabel(t, textvariable=v_aviso_tema, font=F(11), text_color=C["texto2"], anchor="w").grid(
            row=1, column=0, sticky="w", padx=20, pady=(0, 14))
        b_reiniciar_tema = boton(t, "Reiniciar ahora", primario=True, ancho=140)

        seccion(p, "Actualizaciones", 4)
        t = Tarjeta(p, 5)
        b_buscar_act = boton(t, "Buscar actualizaciones", ancho=190)
        b_pdf_def = boton(t, "Abrir los PDF con PdFOL", ancho=190)
        t.fila(f"Versión: {VERSION}  ·  by {AUTOR}", b_buscar_act,
               "Al abrir, PdFOL revisa si hay una versión nueva (si no hay internet, no molesta). "
               "Actualizar nunca es obligatorio y conserva tus perfiles.")
        t.fila("Programa para los PDF", b_pdf_def,
               "Que Windows abra los PDF con PdFOL (doble clic en un PDF). Disponible en la versión instalada."
               if not es_instalado() else "Que Windows abra los PDF con PdFOL al hacer doble clic en un PDF.")
        b_buscar_act.configure(command=lambda: buscar_actualizacion(manual=True))
        b_reiniciar_tema.configure(command=reiniciar_pdfol)
        b_pdf_def.configure(command=abrir_siempre_con_pdfol)
        for n_, b_ in botones_tema.items():
            b_.configure(border_color=C["acento"] if n_ == V["apariencia"].get() else C["tarjeta"])
    por_armar["apariencia"] = _armar_apariencia

    # ================================================== v2.6: PANEL FIRMAR Y SELLAR
    v_fcat = tk.StringVar(value="Firmas")
    caja_firmas = None
    b_agregar_firma = None
    v_firma_info = tk.StringVar(value="")

    def _armar_firmar():
        nonlocal caja_firmas, b_agregar_firma
        p = pagina_nueva("firmar")
        t = Tarjeta(p, 0)
        seg_ = segmentado(t, ["Firmas", "Sellos"], v_fcat, ancho=200, cmd=lambda _v: dibujar_firmas_panel())
        t.fila("Elegí", seg_)
        seccion(p, "Guardadas", 1)
        t = Tarjeta(p, 2)
        caja_firmas = ctk.CTkFrame(t, fg_color="transparent")
        caja_firmas.grid(row=0, column=0, columnspan=2, sticky="ew", padx=14, pady=(12, 6))
        b_agregar_firma = boton(t, "Agregar desde imagen…", primario=True, ancho=200,
                                command=lambda: agregar_firma_dialogo())
        b_agregar_firma.grid(row=1, column=0, columnspan=2, sticky="w", padx=14, pady=(4, 14))
        ctk.CTkLabel(p, textvariable=v_firma_info, font=F(11), text_color=C["texto2"], anchor="w", justify="left",
                     wraplength=440).grid(row=3, column=0, sticky="ew", padx=18, pady=(8, 4))
        ctk.CTkLabel(p, text="Cómo se usa: hacé clic en la hoja donde va. Arrastrala para moverla y tirá de la "
                             "esquina para cambiar el tamaño. Clic derecho o Supr la quita. «Guardar cambios» "
                             "(arriba) la deja fija en el PDF.\n\nEs una firma en imagen, no un certificado digital.",
                     font=F(11), text_color=C["texto2"], anchor="w", justify="left", wraplength=440).grid(
            row=4, column=0, sticky="ew", padx=18, pady=(4, 20))
        dibujar_firmas_panel()

    por_armar["firmar"] = _armar_firmar

    # ================================================== v2.6: PANEL TEXTO
    v_tmodo = tk.StringVar(value="Agregar")
    _f0 = almacen.datos.get("texto_fuente", "Arial")
    _f0 = {"Helvetica": "Arial", "Times": "Times New Roman", "Courier": "Courier New"}.get(_f0, _f0)
    v_tfuente = tk.StringVar(value=_f0)  # se revisa que este instalada al armar el panel
    v_tneg = tk.BooleanVar(value=bool(almacen.datos.get("texto_negrita", False)))
    v_tcur = tk.BooleanVar(value=bool(almacen.datos.get("texto_cursiva", False)))
    v_talc = tk.StringVar(value=almacen.datos.get("texto_alcance", "Párrafo"))
    # v2.7: mas herramientas de texto
    v_tsub = tk.BooleanVar(value=False)
    v_ttach = tk.BooleanVar(value=False)
    v_tfondo = tk.BooleanVar(value=False)
    ALINEAS = {"Izq.": "izq", "Centro": "centro", "Der.": "der", "Justif.": "just"}
    v_talin = tk.StringVar(value="Izq.")
    v_tinter = tk.StringVar(value="Original")
    v_ttam = tk.StringVar(value=str(almacen.datos.get("texto_tam", 12)))
    texto_col = {"rgb": tuple(almacen.datos.get("texto_color", (0, 0, 0))), "puntos": []}
    v_texto_ayuda = tk.StringVar(value="")

    def _armar_texto():
        p = pagina_nueva("texto")
        t = Tarjeta(p, 0)
        t.fila("Qué hacer", segmentado(t, ["Agregar", "Cambiar"], v_tmodo, ancho=200, cmd=lambda _v: ayuda_texto()))
        t.fila("Al cambiar, tomar", segmentado(t, ["Párrafo", "Renglón"], v_talc, ancho=200,
                                               cmd=lambda _v: (almacen.datos.update(texto_alcance=v_talc.get()),
                                                               ayuda_texto())))
        ctk.CTkLabel(p, textvariable=v_texto_ayuda, font=F(11), text_color=C["texto2"], anchor="w", justify="left",
                     wraplength=440).grid(row=1, column=0, sticky="ew", padx=18, pady=(4, 6))
        seccion(p, "Letra", 2)
        t = Tarjeta(p, 3)
        disp_ = fuentes_ed_disponibles()
        if v_tfuente.get() not in disp_:
            v_tfuente.set("Arial" if "Arial" in disp_ else "Helvetica (PDF)")
        t.fila("Fuente", menu(t, disp_, v_tfuente, 200, cmd=lambda _v: estilo_texto_cambio()))
        caja_e = ctk.CTkFrame(t, fg_color="transparent")
        for txt_, var_, fnt_, tip_ in (("N", v_tneg, F(13, "bold"), "Negrita"),
                                       ("C", v_tcur, ctk.CTkFont(family=FAM, size=13, slant="italic"), "Cursiva"),
                                       ("S", v_tsub, ctk.CTkFont(family=FAM, size=13, underline=True), "Subrayado"),
                                       ("T", v_ttach, ctk.CTkFont(family=FAM, size=13, overstrike=True), "Tachado")):
            b_ = ctk.CTkButton(caja_e, text=txt_, width=34, height=30, corner_radius=7, font=fnt_,
                               fg_color=C["suave"], hover_color=C["suave_h"], text_color=C["texto"],
                               command=lambda v__=var_: v__.set(not v__.get()))
            b_.pack(side="left", padx=2)

            def pintar_(*_a, b__=b_, v__=var_):
                b__.configure(fg_color=C["acento"] if v__.get() else C["suave"],
                              text_color="#FFFFFF" if v__.get() else C["texto"])
            var_.trace_add("write", pintar_)
            pintar_()
        t.fila("Estilo", caja_e)
        t.fila("Tamaño (pt)", Contador(t, v_ttam, 4, 144, ancho=50, decimales=True))
        t.fila("Alineación", segmentado(t, list(ALINEAS), v_talin, ancho=200, cmd=lambda _v: estilo_texto_cambio()))
        t.fila("Interlineado", menu(t, list(INTERLINEADOS), v_tinter, 110, cmd=lambda _v: estilo_texto_cambio()),
               ayuda="«Original»: el del PDF (o 1,25 en texto nuevo)")
        t.fila("Fondo blanco", switch(t, v_tfondo), ayuda="Tapa lo que hay debajo (texto nuevo)")
        caja_c = ctk.CTkFrame(t, fg_color="transparent")
        texto_col["puntos"] = []
        for _n, rgb in COLORES_FOLIO:
            hx = "#%02x%02x%02x" % rgb
            b_ = ctk.CTkButton(caja_c, text="", width=22, height=22, corner_radius=11, fg_color=hx, hover_color=hx,
                               border_width=0, border_color=C["acento"], command=lambda c_=rgb: color_texto(c_))
            b_.pack(side="left", padx=3)
            texto_col["puntos"].append((b_, rgb))

        def otro_color():
            from tkinter import colorchooser
            r_ = colorchooser.askcolor(color="#%02x%02x%02x" % texto_col["rgb"], parent=raiz, title="Color del texto")
            if r_ and r_[0]:
                color_texto(tuple(int(v_) for v_ in r_[0]))
        boton(caja_c, "Otro…", ancho=60, command=otro_color).configure(height=24, font=F(11))
        caja_c.winfo_children()[-1].pack(side="left", padx=(8, 0))
        t.fila("Color", caja_c, abajo=True)
        seccion(p, "Editar", 5)
        t = Tarjeta(p, 6)
        caja_b = ctk.CTkFrame(t, fg_color="transparent")
        for txt_, cmd_ in (("Deshacer", lambda: deshacer_edicion()), ("Rehacer", lambda: rehacer_edicion()),
                           ("Duplicar", lambda: duplicar_editado()), ("Quitar", lambda: quitar_editado())):
            boton(caja_b, txt_, ancho=84, command=cmd_).pack(side="left", padx=2)
        t.fila("", caja_b, abajo=True)
        ctk.CTkLabel(p, text="Atajos: Ctrl+Z deshace · Ctrl+Y rehace · Supr quita · flechas mueven el texto elegido "
                             "(Shift: más rápido) · doble clic corrige el texto.",
                     font=F(11), text_color=C["texto2"], anchor="w", justify="left", wraplength=440).grid(
            row=7, column=0, sticky="ew", padx=18, pady=(4, 0))
        ctk.CTkLabel(p, text="«Cambiar» usa la misma fuente del texto original si está instalada en Windows; si no, la "
                             "más parecida. Podés elegir otra en «Fuente». Nada se escribe en el PDF hasta «Guardar cambios».",
                     font=F(11), text_color=C["texto2"], anchor="w", justify="left", wraplength=440).grid(
            row=4, column=0, sticky="ew", padx=18, pady=(10, 20))
        color_texto(texto_col["rgb"], aplicar=False)
        ayuda_texto()

    por_armar["texto"] = _armar_texto
    for v_ in (v_tneg, v_tcur, v_ttam, v_tsub, v_ttach, v_tfondo):
        v_.trace_add("write", lambda *_: estilo_texto_cambio())

    # ================================================== PAGINA: ORGANIZAR
    # Miniaturas livianas: se dibujan solo las que se ven (y algunas mas), en un hilo aparte,
    # y se guardan como maximo ORG_CACHE en memoria. El PDF nuevo se arma copiando paginas.
    ORG_CACHE = 400
    TAMS_MINI = {"Chicas": 96, "Medianas": 132, "Grandes": 190}
    org = {"fuentes": [], "orden": [], "sel": set(), "ancla": None, "pila": [], "copiado": [],
           "ruta": None, "cache": {}, "lru": [], "fotos": {}, "pend": set(), "arrastre": None,
           "geo": None, "guardando": False, "gen": 0,
           "origen": {}, "preparar": False, "preparando": False}

    def org_nombre(r_):
        return os.path.basename(org["origen"].get(r_, r_))
    org_cola = queue.Queue()
    # v4.0: las miniaturas las dibuja otro proceso (arranca la primera vez que se usa Organizar)
    org_q_ent, org_q_sal = mp.Queue(), mp.Queue()
    org_proc = {"p": None}

    class _PedidosOrg:
        def put(self, msg):
            if msg[0] == "cerrar" and not org_proc["p"]:
                org_pedidos_hilo.put(msg)
                return
            if org_proc["p"] is None:
                try:
                    org_proc["p"] = mp.Process(target=_proceso_miniaturas_org, args=(org_q_ent, org_q_sal),
                                               daemon=True)
                    org_proc["p"].start()
                except Exception:
                    org_proc["p"] = False
            if org_proc["p"] is False:  # sin proceso: se dibuja aca (como antes)
                org_pedidos_hilo.put(msg)
                return
            if msg[0] != "cerrar" and msg[0][0] != org_proc.get("gen"):
                org_proc["gen"] = msg[0][0]
                org_q_ent.put(("gen", msg[0][0]))
            org_q_ent.put(msg)
    org_pedidos = _PedidosOrg()
    org_pedidos_hilo = queue.Queue()
    v_org_info = tk.StringVar(value="")
    v_org_tam = tk.StringVar(value="Medianas")

    def org_hilo_miniaturas():
        abiertos = {}
        while True:
            clave, ruta_f, pag, ancho = org_pedidos_hilo.get()
            if clave == "cerrar":  # v3.5: soltar el archivo (se va a reemplazar)
                try:
                    abiertos.pop(ruta_f).close()
                except Exception:
                    pass
                continue
            try:
                d = abiertos.get(ruta_f)
                if d is None:
                    d = abiertos[ruta_f] = fitz.open(ruta_f)
                pg = d[pag]
                z = ancho / max(pg.rect.width, pg.rect.height)
                pix = pg.get_pixmap(matrix=fitz.Matrix(z, z), alpha=False)
                img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                org_cola.put((clave, img))
            except Exception:
                org_cola.put((clave, None))

    threading.Thread(target=org_hilo_miniaturas, daemon=True).start()

    p = ctk.CTkFrame(contenido, fg_color=C["fondo"], corner_radius=0)
    p.grid_columnconfigure(0, weight=1)
    p.grid_rowconfigure(2, weight=1)
    paginas["organizar"] = p
    barra_org = ctk.CTkFrame(p, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
    barra_org.grid(row=0, column=0, sticky="ew", padx=24, pady=(4, 6))

    # barra con iconos (como la de arriba): una fila, agrupada. Copiar, Cortar, Pegar y Eliminar van con
    # Ctrl+C / Ctrl+X / Ctrl+V / Supr y con el clic derecho sobre las miniaturas.
    fila1 = ctk.CTkFrame(barra_org, fg_color="transparent")
    fila1.pack(fill="x", padx=10, pady=8)
    b_org = {}
    img_org = {}

    def sep(f_):
        ctk.CTkFrame(f_, width=1, height=40, fg_color=C["borde"]).pack(side="left", padx=3)

    BOTONES_ORG = (("abrir", "Abrir PDF", "abrir", "#2563EB"), ("unir", "Unir PDF", "unir", "#2563EB"), ("|",),
                   ("ver", "Ver página", "ver", "#06B6D4"), ("visor_v", "En el visor", "visor", "#06B6D4"), ("|",),
                   ("rot_i", "Girar izq.", "girar_i", "#8B5CF6"), ("rot_d", "Girar der.", "girar_d", "#8B5CF6"),
                   ("|",),
                   ("izq", "Atrás", "mover_i", "#F59E0B"), ("der", "Adelante", "mover_d", "#F59E0B"),
                   ("mover_a", "Mover a…", "mover_a", "#F59E0B"), ("|",),
                   ("deshacer", "Deshacer", "deshacer", "#64748B"), ("rehacer", "Rehacer", "rehacer", "#64748B"),
                   ("todo", "Original", "deshacer", "#64748B"), ("|",),
                   ("limpiar", "Limpiar", "limpiar", "#E0607E"), ("|",),
                   ("ayuda", "Ayuda", "ayuda", "#64748B"))
    for it_ in BOTONES_ORG:
        if it_[0] == "|":
            sep(fila1)
            continue
        clave, texto, glifo, color_ = it_
        im_ = _icono(glifo, color_, 78)
        img_org[clave] = (ctk.CTkImage(im_, size=(26, 26)), ctk.CTkImage(_icono_apagado(im_), size=(26, 26)))  # v3.3: im_ grande
        b_ = ctk.CTkButton(fila1, text=texto, image=img_org[clave][0], compound="top", width=48,
                           height=56, corner_radius=9, font=F(10), fg_color="transparent", hover_color=C["suave"],
                           text_color=C["texto"], text_color_disabled=C["texto2"])
        b_.pack(side="left", padx=1)
        b_org[clave] = b_
    # tamano de miniaturas y «Ver como hoja impresa»: a la derecha, debajo de la barra
    caja_der_org = ctk.CTkFrame(p, fg_color="transparent")
    caja_der_org.grid(row=1, column=0, sticky="ne", padx=24, pady=(0, 4))
    menu(caja_der_org, list(TAMS_MINI), v_org_tam, ancho=112, cmd=lambda _: org_dibujar(True)).pack(side="right")

    def casilla_impresa(master, cmd=None, texto="Ver como hoja impresa"):
        return ctk.CTkCheckBox(master, text=texto, variable=V["girar_prev"], font=F(12),
                               text_color=C["texto"], fg_color=C["acento"], hover_color=C["acento_h"],
                               border_color=C["texto2"], checkbox_width=18, checkbox_height=18, border_width=2,
                               command=cmd)
    casilla_impresa(caja_der_org).pack(side="right", padx=(0, 12))
    V["girar_prev"].trace_add("write", lambda *_: (org_dibujar(True), actualizar_ejemplo()))

    caja_info = ctk.CTkFrame(p, fg_color="transparent")
    caja_info.grid(row=1, column=0, sticky="ew", padx=28, pady=(0, 6))
    caja_der_org.lift()
    l_org_info = ctk.CTkLabel(caja_info, textvariable=v_org_info, font=F(11), text_color=C["texto2"], anchor="w",
                              justify="left", wraplength=800)
    l_org_info.pack(fill="x")
    # colores por documento (fondo sutil, barra) en claro y oscuro
    COLORES_DOC = [(("#EAF1FB", "#5B8DEF"), ("#1F2B40", "#6F9BF2")), (("#FDF3E2", "#E0A030"), ("#382E1D", "#E8B04A")),
                   (("#E7F6EE", "#3DAA6D"), ("#1C3428", "#4FC083")), (("#F2ECFA", "#9B6BD6"), ("#2E2640", "#B08AE4")),
                   (("#FBEAEF", "#E0607E"), ("#3A2229", "#EC7C96")), (("#E4F5F5", "#2BA3A3"), ("#1B3535", "#3CC0C0"))]

    def color_doc(fid, cual):
        par = COLORES_DOC[fid % len(COLORES_DOC)][1 if modo_oscuro() else 0]
        return par[0 if cual == "fondo" else 1]
    p.bind("<Configure>", lambda e: l_org_info.configure(wraplength=max(300, e.width - 470)), add="+")
    marco_cv = ctk.CTkFrame(p, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
    marco_cv.grid(row=2, column=0, sticky="nsew", padx=24, pady=(0, 14))
    marco_cv.grid_columnconfigure(0, weight=1)
    marco_cv.grid_rowconfigure(0, weight=1)
    cv = tk.Canvas(marco_cv, highlightthickness=0, bd=0, takefocus=1)
    cv.grid(row=0, column=0, sticky="nsew", padx=(8, 0), pady=8)
    sb_org = Desliz(marco_cv, command=cv.yview, button_color=C["suave_h"],
                              button_hover_color=C["borde"])
    sb_org.grid(row=0, column=1, sticky="ns", padx=(0, 4), pady=8)
    cv.configure(yscrollcommand=sb_org.set)

    # ---- modelo
    def org_cargar(rutas, agregar=False, pos=None):
        nuevos = []
        for r_ in rutas:
            try:
                n = contar_paginas(r_)
            except Exception:
                messagebox.showerror(NOMBRE, f"No se pudo abrir:\n{r_}")
                continue
            if r_ in org["fuentes"]:
                fid = org["fuentes"].index(r_)
            else:
                org["fuentes"].append(r_)
                fid = len(org["fuentes"]) - 1
            nuevos += [(fid, k, 0) for k in range(n)]
        if not nuevos:
            return
        if agregar:
            org_guardar_paso()
            if pos is None:
                pos = (max(org["sel"]) + 1) if org["sel"] else len(org["orden"])
            pos = max(0, min(pos, len(org["orden"])))
            org["orden"][pos:pos] = nuevos
            org["sel"] = set(range(pos, pos + len(nuevos)))
        else:
            org["orden"] = nuevos
            org["original"] = list(nuevos)
            org["pila"] = []
            org["sel"] = set()
        org_dibujar(True)
        if agregar:
            org_ver_indice(pos)

    def org_entrar():
        ruta_doc = V["ruta"].get().strip().strip('"')
        if ruta_doc and os.path.isfile(ruta_doc) and ruta_doc != org["ruta"]:
            org["ruta"] = ruta_doc
            org["fuentes"] = []
            org["gen"] += 1
            org["pend"].clear()
            org["cache"].clear()
            org["lru"].clear()
            org_cargar([ruta_doc])
        else:
            org_dibujar(True)
        cv.focus_set()

    def org_guardar_paso():
        org["pila"].append((list(org["orden"]), set(org["sel"])))
        del org["pila"][:-60]
        org["rehacer"] = []  # un cambio nuevo borra lo que se podia rehacer

    def org_deshacer(*_):
        if org["pila"]:
            org.setdefault("rehacer", []).append((list(org["orden"]), set(org["sel"])))
            org["orden"], org["sel"] = org["pila"].pop()
            org_dibujar()
            org_info()

    def org_rehacer(*_):
        if org.get("rehacer"):
            org["pila"].append((list(org["orden"]), set(org["sel"])))
            org["orden"], org["sel"] = org["rehacer"].pop()
            org_dibujar()
            org_info()

    def org_original():
        if org.get("original") and org["orden"] != org["original"]:
            org_guardar_paso()
            org["orden"] = list(org["original"])
            org["sel"] = set()
            org_dibujar()

    def sel_ordenada():
        return sorted(org["sel"])

    def org_mover_a(destino):
        """mueve la seleccion para que empiece en 'destino' (indice en la lista sin la seleccion)."""
        s = sel_ordenada()
        if not s:
            return
        bloque = [org["orden"][i] for i in s]
        resto = [x for i, x in enumerate(org["orden"]) if i not in org["sel"]]
        destino = max(0, min(destino, len(resto)))
        nuevo = resto[:destino] + bloque + resto[destino:]
        if nuevo == org["orden"]:
            return
        org_guardar_paso()
        org["orden"] = nuevo
        org["sel"] = set(range(destino, destino + len(bloque)))
        org_dibujar()
        org_ver_indice(destino)

    def org_paso(d):
        s = sel_ordenada()
        if not s:
            return
        antes = sum(1 for i in range(s[0]) if i not in org["sel"])
        org_mover_a(antes + d)

    def org_mover_dialogo():
        s = sel_ordenada()
        if not s:
            return
        dlg = ctk.CTkInputDialog(title=NOMBRE, text=f"Mover {len(s)} página(s) a la posición (1 a {len(org['orden'])}):")
        t_ = dlg.get_input()
        try:
            pos = int(str(t_).strip())
        except Exception:
            return
        org_mover_a(pos - 1)

    def org_copiar(cortar=False):
        s = sel_ordenada()
        if not s:
            return
        # se guarda la ruta (no el numero de documento): asi se puede pegar en otra pestana
        org["copiado"] = [(org["fuentes"][f_], p_, r_) for f_, p_, r_ in (org["orden"][i] for i in s)]
        if cortar:
            org_eliminar()
            v_estado.set(f"{len(s)} página(s) cortadas: elegí dónde y presioná «Pegar».")
        else:
            v_estado.set(f"{len(s)} página(s) copiadas: elegí dónde y presioná «Pegar».")

    def org_pegar(*_):
        if not org["copiado"]:
            return
        org_guardar_paso()
        pos = (max(org["sel"]) + 1) if org["sel"] else len(org["orden"])
        nuevos = []
        for ruta_, p_, r_ in org["copiado"]:
            if ruta_ not in org["fuentes"]:
                org["fuentes"].append(ruta_)
            nuevos.append((org["fuentes"].index(ruta_), p_, r_))
        org["orden"][pos:pos] = nuevos
        org["sel"] = set(range(pos, pos + len(nuevos)))
        v_estado.set(f"{len(nuevos)} página(s) pegadas.")
        org_dibujar()
        org_ver_indice(pos)

    def org_eliminar(*_):
        s = sel_ordenada()
        if not s:
            return
        if len(s) == len(org["orden"]):
            messagebox.showinfo(NOMBRE, "El PDF tiene que quedar con al menos una página.")
            return
        org_guardar_paso()
        org["orden"] = [x for i, x in enumerate(org["orden"]) if i not in org["sel"]]
        org["sel"] = {min(s[0], len(org["orden"]) - 1)}
        org["ancla"] = None
        org_dibujar()

    def org_girar(g):
        if not org["sel"]:
            return
        org_guardar_paso()
        for i in org["sel"]:
            f_, p_, r_ = org["orden"][i]
            org["orden"][i] = (f_, p_, (r_ + g) % 360)
        org_dibujar()

    # ---- dibujo
    def org_geometria():
        tam = TAMS_MINI.get(v_org_tam.get(), 132)
        celda_w, celda_h = tam + 28, tam + 42
        ancho = max(cv.winfo_width(), celda_w)
        cols = max(1, (ancho - 10) // celda_w)
        margen = max(6, (ancho - cols * celda_w) // 2)
        return tam, celda_w, celda_h, cols, margen

    def org_pos(i, geo):
        tam, cw, ch, cols, mx = geo
        return mx + (i % cols) * cw, 8 + (i // cols) * ch

    def org_mini(fid, pag, rot, tam):
        k = (org["gen"], fid, pag, tam)
        img = org["cache"].get(k)
        if img is None:
            if k not in org["pend"]:
                org["pend"].add(k)
                org_pedidos.put((k, org["fuentes"][fid], pag, tam))
            return None
        if k in org["lru"]:
            org["lru"].remove(k)
        org["lru"].append(k)
        img = img.rotate(-rot, expand=True) if rot else img
        if V["girar_prev"].get() and img.width > img.height:
            img = img.rotate(90, expand=True)  # hoja parada: encabezado hacia la perforacion
        return img

    def org_dibujar(rehacer=False, *_):
        org_cambio()
        if app["pagina"] != "organizar":
            return
        geo = org_geometria()
        org["geo"] = geo
        tam, cw, ch, cols, mx = geo
        n = len(org["orden"])
        cv.configure(bg=col("tarjeta"))
        filas = (n + cols - 1) // cols
        cv.configure(scrollregion=(0, 0, cv.winfo_width(), max(filas * ch + 16, cv.winfo_height())))
        cv.delete("all")
        previas, org["fotos"] = org["fotos"], {}
        if not n:
            cv.create_text(cv.winfo_width() // 2, 120, text="Abrí un PDF (o elegilo en Documento) para ver sus páginas.",
                           fill=col("texto2"), font=(FAM, 12))
            org_info()
            return
        y0 = cv.canvasy(0)
        y1 = y0 + cv.winfo_height()
        f0 = max(0, int(y0 // ch) - 1)
        f1 = min(filas, int(y1 // ch) + 2)
        multi = len(org["fuentes"]) > 1
        for i in range(f0 * cols, min(n, f1 * cols)):
            fid, pag, rot = org["orden"][i]
            x, y = org_pos(i, geo)
            sel = i in org["sel"]
            if multi and not sel:  # fondo sutil del color de su documento
                cv.create_rectangle(x + 4, y + 2, x + cw - 8, y + ch - 8, outline="", fill=color_doc(fid, "fondo"),
                                    tags=("celda", f"i{i}"))
            cv.create_rectangle(x + 2, y, x + cw - 6, y + ch - 6, outline=col("acento") if sel else "",
                                fill=col("suave") if sel else "", width=2, tags=("celda", f"i{i}"))
            if multi:  # barra del documento, visible tambien si esta seleccionada
                cv.create_rectangle(x + 4, y + ch - 13, x + cw - 8, y + ch - 9, outline="",
                                    fill=color_doc(fid, "barra"), tags=("celda", f"i{i}"))
            img = org_mini(fid, pag, rot, tam)
            cx, cy = x + (cw - 4) // 2, y + 6 + tam // 2
            if img is None:
                cv.create_rectangle(cx - tam * 0.35, cy - tam * 0.48, cx + tam * 0.35, cy + tam * 0.48,
                                    outline=col("borde"), fill=col("campo"), tags=("celda", f"i{i}"))
            else:
                kf = (org["gen"], fid, pag, tam, rot, V["girar_prev"].get())
                ft = previas.get(kf) or org["fotos"].get(kf) or foto_tk(img)
                org["fotos"][kf] = ft
                cv.create_image(cx, cy, image=ft, tags=("celda", f"i{i}"))
                w_, h_ = img.size
                cv.create_rectangle(cx - w_ // 2, cy - h_ // 2, cx + w_ // 2, cy + h_ // 2, outline=col("borde"),
                                    tags=("celda", f"i{i}"))
            etq = f"{i + 1}"
            if multi or (fid, pag) != (0, i):
                etq += f"   (orig. {'ABCDEFGHIJKLMNOPQRSTUVWXYZ'[fid % 26] + '·' if multi else ''}{pag + 1})"
            cv.create_text(cx, y + tam + 20, text=etq, fill=col("acento") if sel else col("texto2"),
                           font=(FAM, 10, "bold" if sel else "normal"), tags=("celda", f"i{i}"))
        # limitar memoria de miniaturas
        while len(org["lru"]) > ORG_CACHE:
            org["cache"].pop(org["lru"].pop(0), None)
        org_info()

    def org_cambio():
        """El orden de la pestana activa cambio: el visor y las miniaturas lo muestran."""
        vis["orgver"] += 1
        vis["seleccion"] = None
        if vis.get("busq") and vis["busq"]["ver"] != vis["orgver"] and vis["busq"]["tab"] == (pest_activa() or {}).get("id"):
            busq_cerrar()
        if app["pagina"] == "visor":
            visor_pedir_dibujo()
            mini_pedir_dibujo()
        marca = tiene_organizado(pest_activa()) if pest_activa() else None
        try:
            refrescar_boton_guardar()
        except NameError:
            pass
        if marca != vis.get("marca_org"):
            vis["marca_org"] = marca
            raiz.after_idle(dibujar_pestanas)

    def org_info():
        n = len(org["orden"])
        if not n:
            v_org_info.set("")
        else:
            txt = f"{n} páginas"
            if len(org["fuentes"]) > 1:
                txt += f" de {len(org['fuentes'])} PDF"
            txt += f"  ·  {len(org['sel'])} seleccionadas" if org["sel"] else ""
            v_org_info.set(txt)
        # leyenda de colores por documento
        firma = (tuple(org["fuentes"]) if len(org["fuentes"]) > 1 and n else (), modo_oscuro())
        if firma != org.get("firma_leyenda"):
            org["firma_leyenda"] = firma
            for w_ in leyenda.winfo_children():
                w_.destroy()
            if firma[0]:  # uno por renglon, en la columna izquierda
                for fid, r_ in enumerate(org["fuentes"]):
                    item = ctk.CTkFrame(leyenda, fg_color="transparent")
                    item.pack(fill="x", pady=(0, 3))
                    ctk.CTkFrame(item, width=14, height=14, corner_radius=4, fg_color=color_doc(fid, "barra")).pack(
                        side="left", padx=(0, 6))
                    nom = org_nombre(r_)
                    ctk.CTkLabel(item, text=f"{'ABCDEFGHIJKLMNOPQRSTUVWXYZ'[fid % 26]} · "
                                            f"{nom if len(nom) <= 24 else nom[:22] + '…'}",
                                 font=F(11), text_color=C["texto"], anchor="w").pack(side="left")
                leyenda.configure(height=min(170, 19 * len(org["fuentes"])))
                l_archivos_tit.pack(fill="x", padx=14, pady=(0, 4))
                leyenda.pack(fill="x", padx=(10, 4), pady=(0, 8), after=l_archivos_tit)
            else:
                leyenda.pack_forget()
                l_archivos_tit.pack_forget()

        hay, s = n > 0, bool(org["sel"])
        if not app["ocupado"]:  # el boton Procesar de abajo trabaja sobre lo organizado
            algo_ = V["apl"].get() or V["fol"].get() or V["comp"].get()
            hay_doc = bool(V["ruta"].get().strip())
            listo_ = (hay_doc and algo_ and (not V["apl"].get() or app["scores"] is not None)) or (org_activo() and algo_)
            b_procesar.configure(state="normal" if listo_ else "disabled")
            b_analizar.configure(state="normal" if (V["apl"].get() and hay_doc and not org_activo()) else "disabled")
        for k_, ok in (("ver", s), ("visor_v", hay), ("izq", s), ("der", s), ("mover_a", s), ("rot_i", s), ("rot_d", s),
                       ("deshacer", bool(org["pila"])), ("rehacer", bool(org.get("rehacer"))),
                       ("todo", hay and org["orden"] != org.get("original")),
                       ("unir", hay and not org["preparando"]),
                       ("limpiar", hay and not org["preparando"] and not app["ocupado"]), ("abrir", not org["preparando"] and not hay),
                       ):
            if b_org[k_].cget("state") != ("normal" if ok else "disabled"):
                b_org[k_].configure(state="normal" if ok else "disabled", image=img_org[k_][0 if ok else 1])

    def org_ver_indice(i):
        geo = org["geo"] or org_geometria()
        _, y = org_pos(i, geo)
        alto = max(1, float(cv.cget("scrollregion").split()[3]) if cv.cget("scrollregion") else 1)
        y0, y1 = cv.canvasy(0), cv.canvasy(0) + cv.winfo_height()
        if y < y0 or y + geo[2] > y1:
            cv.yview_moveto(max(0, (y - 20) / alto))
            org_dibujar()

    # ---- raton y teclado
    def org_indice(ev):
        geo = org["geo"]
        if not geo:
            return None
        tam, cw, ch, cols, mx = geo
        x, y = cv.canvasx(ev.x), cv.canvasy(ev.y)
        c_ = int((x - mx) // cw)
        f_ = int((y - 8) // ch)
        if c_ < 0 or c_ >= cols or f_ < 0:
            return None
        rx = x - (mx + c_ * cw)
        if rx < 10 or rx > cw - 14:
            return None
        i = f_ * cols + c_
        return i if i < len(org["orden"]) else None

    def org_hueco(ev):
        """posicion de insercion (0..n) mas cercana al puntero."""
        geo = org["geo"]
        tam, cw, ch, cols, mx = geo
        x, y = cv.canvasx(ev.x), cv.canvasy(ev.y)
        f_ = max(0, int((y - 8) // ch))
        c_ = int(round((x - mx) / cw))
        c_ = max(0, min(cols, c_))
        return max(0, min(len(org["orden"]), f_ * cols + c_))

    def org_press(ev):
        cv.focus_set()
        i = org_indice(ev)
        ctrl = bool(ev.state & 0x4)
        shift = bool(ev.state & 0x1)
        if i is None:  # espacio vacio: empezar a sombrear un recuadro
            base = set(org["sel"]) if (ctrl or shift) else set()
            if not base:
                org["sel"] = set()
                org_dibujar()
            org["arrastre"] = {"marco": True, "x0": cv.canvasx(ev.x), "y0": cv.canvasy(ev.y), "base": base,
                               "ctrl": ctrl}
            return
        if shift and org["ancla"] is not None:
            a, b = sorted((org["ancla"], i))
            org["sel"] = set(range(a, b + 1)) | (org["sel"] if ctrl else set())
        elif ctrl:
            org["sel"] ^= {i}
            org["ancla"] = i
        elif i not in org["sel"]:
            org["sel"] = {i}
            org["ancla"] = i
        else:
            org["ancla"] = i
        org["arrastre"] = {"x": ev.x, "y": ev.y, "i": i, "activo": False, "solo": not ctrl and not shift}
        org_dibujar()

    def org_en_marco(x0, y0, x1, y1):
        tam, cw, ch, cols, mx = org["geo"]
        xa, xb = sorted((x0, x1))
        ya, yb = sorted((y0, y1))
        res = set()
        f0, f1 = max(0, int((ya - 8) // ch)), int((yb - 8) // ch)
        for f_ in range(f0, f1 + 1):
            for c_ in range(cols):
                i = f_ * cols + c_
                if i >= len(org["orden"]):
                    break
                x, y = mx + c_ * cw + 10, 8 + f_ * ch
                if x < xb and x + cw - 24 > xa and y < yb and y + ch - 8 > ya:
                    res.add(i)
        return res

    def org_motion(ev):
        a = org["arrastre"]
        if a and a.get("marco"):
            x1, y1 = cv.canvasx(ev.x), cv.canvasy(ev.y)
            dentro = org_en_marco(a["x0"], a["y0"], x1, y1)
            org["sel"] = (a["base"] ^ dentro) if a["ctrl"] else (a["base"] | dentro)
            org_dibujar()
            cv.create_rectangle(a["x0"], a["y0"], x1, y1, outline=col("acento"), width=1, dash=(4, 2),
                                tags="marco")
            if ev.y < 30:
                cv.yview_scroll(-1, "units")
            elif ev.y > cv.winfo_height() - 30:
                cv.yview_scroll(1, "units")
            return
        if not a or not org["sel"]:
            return
        if not a["activo"] and abs(ev.x - a["x"]) + abs(ev.y - a["y"]) < 8:
            return
        a["activo"] = True
        cv.configure(cursor="fleur")
        h = org_hueco(ev)
        geo = org["geo"]
        tam, cw, ch, cols, mx = geo
        x = mx + (h % cols) * cw if h % cols or h == 0 else mx + cols * cw
        y = 8 + (h // cols) * ch if h % cols or h == 0 else 8 + (h // cols - 1) * ch
        cv.delete("guia")
        cv.create_line(x - 2, y + 4, x - 2, y + ch - 10, fill=col("acento"), width=4, tags="guia")
        # desplazamiento automatico cerca de los bordes
        if ev.y < 30:
            cv.yview_scroll(-1, "units")
            org_dibujar()
        elif ev.y > cv.winfo_height() - 30:
            cv.yview_scroll(1, "units")
            org_dibujar()

    def org_release(ev):
        a = org["arrastre"]
        org["arrastre"] = None
        cv.configure(cursor="")
        cv.delete("guia")
        cv.delete("marco")
        if not a:
            return
        if a.get("marco"):
            if org["sel"]:
                org["ancla"] = min(org["sel"])
            org_dibujar()
            return
        if a["activo"]:
            h = org_hueco(ev)
            antes = sum(1 for k_ in range(h) if k_ not in org["sel"])
            org_mover_a(antes)
        elif a["solo"] and len(org["sel"]) > 1:
            org["sel"] = {a["i"]}
            org_dibujar()

    def org_rueda(ev):
        d = -1 if (getattr(ev, "delta", 0) > 0 or getattr(ev, "num", 0) == 4) else 1
        cv.yview_scroll(d * 2, "units")
        org_dibujar()

    def org_teclas(ev):
        ctrl = bool(ev.state & 0x4)
        k_ = ev.keysym.lower()
        if k_ == "delete":
            org_eliminar()
        elif ctrl and k_ == "z" and ev.state & 0x1:
            org_rehacer()
        elif ctrl and k_ == "z":
            org_deshacer()
        elif ctrl and k_ == "y":
            org_rehacer()
        elif ctrl and k_ == "a":
            org["sel"] = set(range(len(org["orden"])))
            org_dibujar()
        elif ctrl and k_ == "c":
            org_copiar()
        elif ctrl and k_ == "x":
            org_copiar(cortar=True)
        elif ctrl and k_ == "v":
            org_pegar()
        elif k_ in ("left", "right", "up", "down") and org["sel"]:
            cols = org["geo"][3] if org["geo"] else 1
            paso = {"left": -1, "right": 1, "up": -cols, "down": cols}[k_]
            if ctrl:
                org_paso(paso)
            else:
                i = max(0, min(len(org["orden"]) - 1, (max(org["sel"]) if paso > 0 else min(org["sel"])) + paso))
                org["sel"], org["ancla"] = {i}, i
                org_dibujar()
                org_ver_indice(i)
        elif k_ in ("return", "space") and org["sel"]:
            org_visor(min(org["sel"]))

    cv.bind("<ButtonPress-1>", org_press)
    cv.bind("<B1-Motion>", org_motion)
    cv.bind("<ButtonRelease-1>", org_release)
    cv.bind("<Double-Button-1>", lambda ev: org_visor(org_indice(ev)) if org_indice(ev) is not None else None)
    cv.bind("<MouseWheel>", org_rueda)
    cv.bind("<Button-4>", org_rueda)
    cv.bind("<Button-5>", org_rueda)
    cv.bind("<Key>", org_teclas)

    def org_menu(ev):
        cv.focus_set()
        i = org_indice(ev)
        if i is not None and i not in org["sel"]:
            org["sel"], org["ancla"] = {i}, i
            org_dibujar()
        n_ = len(org["sel"])
        m_ = menu_contextual()
        hay_sel = "normal" if n_ else "disabled"
        m_.add_command(label="Ver página", command=lambda: org_visor(min(org["sel"])), state=hay_sel)
        m_.add_command(label="Ver en el visor", command=org_al_visor, state="normal" if org["orden"] else "disabled")
        m_.add_separator()
        m_.add_command(label=f"Copiar ({n_})", acelerador="Ctrl+C", command=org_copiar, state=hay_sel)
        m_.add_command(label=f"Cortar ({n_})", acelerador="Ctrl+X", command=lambda: org_copiar(True), state=hay_sel)
        m_.add_command(label="Pegar después", acelerador="Ctrl+V", command=org_pegar,
                       state="normal" if org.get("copiado") and org["orden"] else "disabled")
        m_.add_separator()
        m_.add_command(label="Girar ↺", command=lambda: org_girar(-90), state=hay_sel)
        m_.add_command(label="Girar ↻", command=lambda: org_girar(90), state=hay_sel)
        m_.add_command(label="Mover a…", command=org_mover_dialogo, state=hay_sel)
        m_.add_separator()
        m_.add_command(label="Deshacer", acelerador="Ctrl+Z", command=org_deshacer,
                       state="normal" if org["pila"] else "disabled")
        m_.add_command(label="Rehacer", acelerador="Ctrl+Y", command=org_rehacer,
                       state="normal" if org.get("rehacer") else "disabled")
        m_.add_separator()
        m_.add_command(label=f"Eliminar ({n_})", acelerador="Supr", command=org_eliminar, state=hay_sel, punto="#EF4444")
        m_.tk_popup(ev.x_root, ev.y_root)

    cv.bind("<Button-3>", org_menu)
    cv.bind("<Configure>", lambda e: raiz.after_idle(org_dibujar))

    def org_scroll(*a):
        cv.yview(*a)
        org_dibujar()

    sb_org.configure(command=org_scroll)

    # ---- visor de pagina
    def org_visor(i):
        if i is None or not org["orden"]:
            return
        w = ctk.CTkToplevel(raiz)
        w.title(f"{NOMBRE} · ver página")
        a0_, b0_, a1_, b1_ = area_monitor(raiz.winfo_rootx() + raiz.winfo_width() // 2,
                                          raiz.winfo_rooty() + raiz.winfo_height() // 2, raiz)  # v4.2: su monitor
        sw_, sh_ = a1_ - a0_, b1_ - b0_
        ww_, hh_ = int(min(1100, sw_ * 0.75)), int(min(1000, sh_ * 0.86))
        w.geometry(f"{ww_}x{hh_}+{a0_ + (sw_ - ww_) // 2}+{b0_ + max(0, (sh_ - hh_) // 2 - 20)}")
        w.configure(fg_color=C["fondo"])
        w.transient(raiz)
        est = {"i": i, "zoom": 1.0, "foto": None, "doc": {}, "trabajo": 0}
        cab = ctk.CTkFrame(w, fg_color="transparent")
        cab.pack(fill="x", padx=14, pady=10)
        v_t = tk.StringVar()
        bp = boton(cab, "◀ Anterior", ancho=100)
        bn = boton(cab, "Siguiente ▶", ancho=100)
        bm = boton(cab, "−", ancho=40)
        bz = boton(cab, "+", ancho=40)
        ba = boton(cab, "Ajustar", ancho=80)
        for b in (bp, bn):
            b.pack(side="left", padx=3)
        ctk.CTkLabel(cab, textvariable=v_t, font=F(13, "bold"), text_color=C["texto"]).pack(side="left", padx=14)
        for b in (ba, bz, bm):
            b.pack(side="right", padx=3)
        casilla_impresa(cab, lambda: render(), "Hoja impresa").pack(side="right", padx=10)
        cvv = tk.Canvas(w, highlightthickness=0, bd=0, bg=col("campo"))
        cvv.pack(fill="both", expand=True, padx=14, pady=(0, 14))
        cola_v = queue.Queue()

        def render():
            est["trabajo"] += 1
            nro = est["trabajo"]
            fid, pag, rot = org["orden"][est["i"]]
            ww, hh = max(cvv.winfo_width(), 300), max(cvv.winfo_height(), 300)
            ruta_f = org["fuentes"][fid]
            parar = V["girar_prev"].get()
            folio_ = None
            if V["fol"].get():  # folio que le tocara a esta pagina en el resultado
                try:
                    cfg_ = cfg_folio()
                    ind_ = rango_folio(cfg_, len(org["orden"]))
                    if est["i"] in ind_:
                        tot_ = int(cfg_["inicio"]) + len(ind_) - 1
                        folio_ = (cfg_, texto_folio(cfg_, int(cfg_["inicio"]) + ind_.index(est["i"]), tot_))
                except Exception:
                    folio_ = None
            v_t.set(f"Página {est['i'] + 1} de {len(org['orden'])}   ·   {org_nombre(ruta_f)}, pág. {pag + 1}"
                    f"   ·   {int(est['zoom'] * 100)} %" + (f"   ·   {folio_[1]}" if folio_ else ""))

            def hilo():
                try:
                    d = fitz.open(ruta_f)
                    pg = d[pag]
                    r_ = pg.rect  # ya incluye el giro propio de la pagina
                    ancho_r, alto_r = (r_.height, r_.width) if rot % 180 else (r_.width, r_.height)
                    z = min(ww / ancho_r, hh / alto_r) * est["zoom"]
                    z = min(z, 6.0)
                    acostada_ = ancho_r > alto_r * 1.001
                    if parar and acostada_:
                        z = min(ww / alto_r, hh / ancho_r) * est["zoom"]
                        z = min(z, 6.0)
                    pix = pg.get_pixmap(matrix=fitz.Matrix(z, z).prerotate(rot), alpha=False)
                    img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                    d.close()
                    if folio_:
                        capa = fitz.open()
                        cp_ = capa.new_page(width=ancho_r, height=alto_r)
                        estampar_folio(cp_, folio_[1], folio_[0])
                        px_ = cp_.get_pixmap(matrix=fitz.Matrix(z, z), alpha=True)
                        ov = Image.frombytes("RGBA", (px_.width, px_.height), px_.samples)
                        capa.close()
                        if ov.size != img.size:
                            ov = ov.resize(img.size)
                        b_ = img.convert("RGBA")
                        b_.alpha_composite(ov)
                        img = b_.convert("RGB")
                    if parar and acostada_:
                        img = img.rotate(90, expand=True)
                    cola_v.put((nro, img))
                except Exception:
                    cola_v.put((nro, None))

            threading.Thread(target=hilo, daemon=True).start()
            cvv.delete("all")
            cvv.create_text(ww // 2, hh // 2, text="Cargando…", fill=col("texto2"), font=(FAM, 12))

        def recibir():
            if not w.winfo_exists():
                return
            try:
                while True:
                    nro, img = cola_v.get_nowait()
                    if nro == est["trabajo"]:
                        cvv.delete("all")
                        if img is None:
                            cvv.create_text(200, 100, text="No se pudo mostrar la página.", fill=col("texto2"))
                        else:
                            est["foto"] = foto_tk(img)
                            ww, hh = cvv.winfo_width(), cvv.winfo_height()
                            cvv.create_image(max(ww // 2, img.width // 2), max(hh // 2, img.height // 2),
                                             image=est["foto"])
                            cvv.configure(scrollregion=(0, 0, max(ww, img.width), max(hh, img.height)))
            except queue.Empty:
                pass
            w.after(100, recibir)

        def ir(d):
            est["i"] = max(0, min(len(org["orden"]) - 1, est["i"] + d))
            render()

        def zoom(f):
            est["zoom"] = 1.0 if f is None else max(0.25, min(8.0, est["zoom"] * f))
            render()

        bp.configure(command=lambda: ir(-1))
        bn.configure(command=lambda: ir(1))
        bz.configure(command=lambda: zoom(1.4))
        bm.configure(command=lambda: zoom(1 / 1.4))
        ba.configure(command=lambda: zoom(None))
        cvv.bind("<ButtonPress-1>", lambda e: cvv.scan_mark(e.x, e.y))
        cvv.bind("<B1-Motion>", lambda e: cvv.scan_dragto(e.x, e.y, gain=1))
        cvv.bind("<MouseWheel>", lambda e: zoom(1.25 if e.delta > 0 else 0.8))
        w.bind("<Left>", lambda e: ir(-1))
        w.bind("<Right>", lambda e: ir(1))
        w.bind("<Prior>", lambda e: ir(-1))
        w.bind("<Next>", lambda e: ir(1))
        w.bind("<Escape>", lambda e: w.destroy())
        w.after(120, render)
        w.after(150, recibir)
        w.after(200, w.focus_force)

    # ---- guardar
    def org_armar(orden, fuentes_, destino, avance=None):
        """Arma el PDF con el orden actual (en un hilo) y marca las paginas que ya vienen listas."""
        docs = {}
        out = fitz.open()
        k = 0
        n = len(orden)
        while k < n:  # copiar por tramos seguidos del mismo PDF y giro
            fid, pag, rot = orden[k]
            j = k
            while j + 1 < n and orden[j + 1] == (fid, pag + (j + 1 - k), rot):
                j += 1
            if fid not in docs:
                docs[fid] = fitz.open(fuentes_[fid])
            ini = len(out)
            out.insert_pdf(docs[fid], from_page=pag, to_page=pag + (j - k))
            if rot:
                for q in range(ini, len(out)):
                    out[q].set_rotation((out[q].rotation + rot) % 360)
            k = j + 1
            if avance:
                avance(k, n)
            else:
                org_cola.put((("prog",), (k, n)))
        listas_f = {fid: leer_listas(fuentes_[fid]) for fid in {f_ for f_, _p, _r in orden}}
        listas = [q for q, (fid, pag, _r) in enumerate(orden) if pag in listas_f[fid]]
        if listas:
            out.xref_set_key(out.pdf_catalog(), CLAVE_LISTAS, f"({texto_rangos(listas)})")
        tmp = destino + ".tmp"
        out.save(tmp, garbage=3, deflate=True)
        out.close()
        for d in docs.values():
            d.close()
        os.replace(tmp, destino)

    def org_activo():
        """Hay paginas organizadas o unidas que difieren del documento: Procesar trabaja sobre ellas."""
        return bool(org["orden"]) and (len(org["fuentes"]) > 1 or org["orden"] != org.get("original")
                                       or bool(org["origen"]))

    def org_pedir_destino(sufijo):
        base = org["origen"].get(org["fuentes"][0], org["fuentes"][0])
        sug = os.path.splitext(os.path.basename(base))[0] + sufijo + ".pdf"
        dest = filedialog.asksaveasfilename(title="Guardar PDF", initialdir=os.path.dirname(base), initialfile=sug,
                                            defaultextension=".pdf", filetypes=[("PDF", "*.pdf")])
        if not dest:
            return None
        if any(os.path.normcase(os.path.abspath(dest)) == os.path.normcase(os.path.abspath(f_))
               for f_ in list(org["fuentes"]) + list(org["origen"].values())):
            messagebox.showerror(NOMBRE, "Elegí otro nombre: el original nunca se reemplaza.")
            return None
        return dest

    def org_guardar():
        if not org["orden"]:
            return
        dest = org_pedir_destino("_unido" if len(org["fuentes"]) > 1 else "_organizado")
        if not dest:
            return
        orden = list(org["orden"])
        fuentes_ = list(org["fuentes"])
        org["guardando"] = True
        org_info()
        v_estado.set("Guardando PDF…")
        barra.set(0)

        def hilo():
            try:
                org_armar(orden, fuentes_, dest)
                org_cola.put((("listo",), dest))
            except Exception as e:
                org_cola.put((("error",), str(e)))

        threading.Thread(target=hilo, daemon=True).start()

    def org_procesar_guardar():
        """Arma el PDF y en el mismo paso aplana lo que falte, comprime y folia, segun la configuracion."""
        if not org["orden"]:
            return
        apl, comp, fol = V["apl"].get(), V["comp"].get(), V["fol"].get()
        if not (apl or comp or fol):
            messagebox.showinfo(NOMBRE, "En Documento › «Qué hacer» activá aplanar, foliar o comprimir.")
            return
        listas_f = {fid: leer_listas(org["fuentes"][fid]) for fid in {f_ for f_, _p, _r in org["orden"]}}
        listas = {q for q, (fid, pag, _r) in enumerate(org["orden"]) if pag in listas_f[fid]}
        n = len(org["orden"])
        pasos_ = []
        if apl:
            pasos_.append("aplanar los planos pesados que falten")
        if comp:
            pasos_.append(f"comprimir ({V['nivel'].get().lower()})")
        if fol:
            pasos_.append("foliar con la configuración de Foliar")
        nota = ""
        if listas and (apl or comp):
            nota = (f"\n\n{len(listas)} de {n} páginas ya entraron aplanadas y comprimidas: no se repiten."
                    if len(listas) < n else "\n\nTodas las páginas ya entraron aplanadas y comprimidas: solo se folia.")
        base_ = org["origen"].get(org["fuentes"][0], org["fuentes"][0])
        dest = nombre_salida(base_)
        if not messagebox.askyesno(NOMBRE, f"Se van a procesar las {n} páginas organizadas: " + ", ".join(pasos_) +
                                   "." + nota + f"\n\nSe guarda como:\n{dest}\n\n¿Continuar?"):
            return
        try:
            folio = cfg_folio() if fol else None
        except Exception:
            messagebox.showerror(NOMBRE, "Revisá la configuración de Foliar.")
            return
        dpi = entero(V["dpi"], DPI_DEFECTO, 72)
        nuc = None if V["nucleos"].get() == "Automático" else entero(V["nucleos"], 1, 1)
        texto_ = V["texto"].get()
        compresion = NIVELES_UI.get(V["nivel"].get(), "equilibrada") if comp else None
        cancelar.clear()
        org["guardando"] = True
        ocupar(True)
        org_info()
        v_estado.set("Paso 1 de 3 · Armando el PDF organizado…")
        barra.set(0)
        org_lanzar("final", {"orden": list(org["orden"]), "fuentes": list(org["fuentes"]), "dest": dest,
                             "tmp": org_tmp(), "apl": apl, "dpi": dpi, "nucleos": nuc, "texto": texto_,
                             "compresion": compresion, "folio": folio})

    def org_recibir():
        hubo = False
        try:  # v4.0: lo que llega del proceso de miniaturas
            for _ in range(60):
                r_ = org_q_sal.get_nowait()
                if len(r_) == 4:
                    org_cola.put((r_[0], Image.frombytes("RGB", (r_[1], r_[2]), r_[3])))
                else:
                    org_cola.put((r_[0], None))
        except Exception:
            pass
        try:
            while True:
                k, v = org_cola.get_nowait()
                if len(k) == 4:  # miniatura
                    org["pend"].discard(k)
                    if v is not None and k[0] == org["gen"]:
                        org["cache"][k] = v
                        org["lru"].append(k)
                        hubo = True
                elif k == ("prog",):
                    barra.set(v[0] / max(1, v[1]))
                    v_detalle.set(f"{v[0]} de {v[1]} páginas")
                elif k == ("listo",):
                    org["guardando"] = False
                    barra.set(1)
                    v_estado.set("PDF guardado.")
                    v_detalle.set(v)
                    app["salida"] = v
                    refrescar()
                    org_info()
                    if messagebox.askyesno(NOMBRE, "PDF guardado.\n\n¿Querés usarlo ahora como documento para "
                                                   "aplanar, foliar o comprimir?"):
                        nuevo_archivo(v)
                        org["ruta"] = None
                elif k == ("fase",):
                    barra.set(v[0])
                    v_detalle.set(f"{v[1]} de {v[2]} páginas")
                elif k == ("prep_estado",):
                    v_estado.set(v)
                elif k == ("prep_prog",):
                    barra.set(v[0] / max(1, v[1]))
                    v_detalle.set(f"{v[0]} de {v[1]} páginas")
                elif k == ("prep_listo",):
                    org["preparando"] = False
                    ocupar(False)
                    barra.set(1)
                    planos = sum(x[2] for x in v)
                    ent, sal = sum(x[3] for x in v), sum(x[4] for x in v)
                    v_estado.set("Listo para organizar.")
                    v_detalle.set(f"{planos} planos aplanados · {ent:.1f} MB → {sal:.1f} MB (copia temporal; "
                                  "el original no se toca)")
                    org["al_terminar"](v)
                    org_info()
                elif k == ("prep_error",):
                    org["preparando"] = False
                    ocupar(False)
                    org_info()
                    if v is None:
                        v_estado.set("Cancelado: no se agregó nada.")
                        v_detalle.set("")
                    else:
                        v_estado.set("Error")
                        messagebox.showerror(NOMBRE, f"No se pudo aplanar y comprimir:\n{v}")
                elif k == ("final",):
                    org["guardando"] = False
                    ocupar(False)
                    barra.set(1)
                    dest_, planos_, fol_, ya_ = v
                    mb = os.path.getsize(dest_) / 1048576
                    v_estado.set("PDF final guardado.")
                    partes = [f"{len(org['orden'])} páginas"]
                    if planos_:
                        partes.append(f"{planos_} planos aplanados")
                    if ya_:
                        partes.append(f"{ya_} ya venían listas")
                    if fol_:
                        partes.append(f"{fol_} foliadas")
                    partes.append(f"{mb:.1f} MB")
                    v_detalle.set("  ·  ".join(partes) + f"\n{dest_}")
                    app["salida"] = dest_
                    refrescar()
                    org_info()
                elif k == ("cancelado_final",):
                    org["guardando"] = False
                    ocupar(False)
                    barra.set(0)
                    v_estado.set("Proceso cancelado.")
                    v_detalle.set("No se generó ningún archivo.")
                    org_info()
                elif k == ("error",):
                    org["guardando"] = False
                    ocupar(False)
                    v_estado.set("Error")
                    org_info()
                    messagebox.showerror(NOMBRE, f"No se pudo guardar el PDF:\n{v}")
        except queue.Empty:
            pass
        if hubo:
            org_dibujar()
        raiz.after(150, org_recibir)

    def org_dialogo(rutas, con_posicion, al_aceptar):
        """Pregunta donde agregar (si con_posicion) y si aplanar y comprimir antes de editar."""
        n = len(org["orden"])
        w = ctk.CTkToplevel(raiz)
        w.title(f"{NOMBRE} · " + ("unir" if con_posicion else "abrir"))
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        nombres = ", ".join(os.path.basename(x) for x in rutas)
        titulo_ = (("¿Dónde querés agregar " + ("el PDF" if len(rutas) == 1 else f"los {len(rutas)} PDF") + "?")
                   if con_posicion else "Abrir para organizar")
        ctk.CTkLabel(w, text=titulo_, font=F(15, "bold"), text_color=C["texto"], anchor="w").pack(
            fill="x", padx=22, pady=(18, 2))
        ctk.CTkLabel(w, text=nombres, font=F(11), text_color=C["texto2"], anchor="w", justify="left",
                     wraplength=440).pack(fill="x", padx=22, pady=(0, 10))
        v_donde = tk.StringVar(value="Después de la página" if org["sel"] else "Al final")
        v_pag = tk.StringVar(value=str(max(org["sel"]) + 1 if org["sel"] else n))
        if con_posicion:
            caja = ctk.CTkFrame(w, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
            caja.pack(fill="x", padx=22, pady=(0, 10))
            for k_, opcion in enumerate(("Al inicio del documento", "Después de la página", "Al final del documento")):
                f_ = ctk.CTkFrame(caja, fg_color="transparent")
                f_.pack(fill="x", padx=14, pady=(10 if k_ == 0 else 2, 10 if k_ == 2 else 2))
                valor = {0: "Al inicio", 1: "Después de la página", 2: "Al final"}[k_]
                ctk.CTkRadioButton(f_, text=opcion, variable=v_donde, value=valor, font=F(13), text_color=C["texto"],
                                   fg_color=C["acento"], hover_color=C["acento_h"]).pack(side="left")
                if k_ == 1:
                    e_ = entrada(f_, v_pag, 70, justify="center")
                    e_.pack(side="left", padx=(8, 4))
                    ctk.CTkLabel(f_, text=f"de {n}", font=F(12), text_color=C["texto2"]).pack(side="left")
                    e_.bind("<FocusIn>", lambda _e: v_donde.set("Después de la página"))
        v_prep = tk.BooleanVar(value=org["preparar"])
        caja2 = ctk.CTkFrame(w, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
        caja2.pack(fill="x", padx=22)
        f2 = ctk.CTkFrame(caja2, fg_color="transparent")
        f2.pack(fill="x", padx=14, pady=10)
        izq = ctk.CTkFrame(f2, fg_color="transparent")
        izq.pack(side="left", fill="x", expand=True)
        ctk.CTkLabel(izq, text="Aplanar y comprimir antes de organizar", font=F(13), text_color=C["texto"],
                     anchor="w").pack(anchor="w")
        ctk.CTkLabel(izq, text=f"Los planos pesados pasan a imagen ({V['dpi'].get()} dpi) y se comprime "
                               f"({V['nivel'].get().lower()}): las miniaturas y la vista cargan mucho más rápido. "
                               "Se usa la configuración de Aplanar y Comprimir.",
                     font=F(11), text_color=C["texto2"], anchor="w", justify="left", wraplength=330).pack(anchor="w")
        switch(f2, v_prep).pack(side="right", padx=(10, 0))
        pie = ctk.CTkFrame(w, fg_color="transparent")
        pie.pack(fill="x", padx=22, pady=16)

        def aceptar():
            pos = None
            if con_posicion:
                d_ = v_donde.get()
                if d_ == "Al inicio":
                    pos = 0
                elif d_ == "Al final":
                    pos = n
                else:
                    try:
                        pos = int(v_pag.get().strip())
                    except ValueError:
                        pos = -1
                    if not 1 <= pos <= n:
                        messagebox.showerror(NOMBRE, f"Escribí un número de página entre 1 y {n}.", parent=w)
                        return
            org["preparar"] = bool(v_prep.get())
            w.destroy()
            al_aceptar(pos, org["preparar"])

        boton(pie, "Agregar" if con_posicion else "Abrir", primario=True, ancho=110, command=aceptar).pack(
            side="right", padx=(8, 0))
        boton(pie, "Cancelar", ancho=100, command=w.destroy).pack(side="right")
        w.bind("<Return>", lambda _e: aceptar())
        w.bind("<Escape>", lambda _e: w.destroy())
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + (raiz.winfo_height() - w.winfo_reqheight()) // 3}")
        w.after(100, lambda: (w.grab_set(), w.focus_force()))

    def org_lanzar(tarea, params):
        """Arranca el trabajo en otro proceso y pasa sus avisos a la interfaz."""
        cola_p = mp.Queue()
        ev = mp.Event()
        pr = mp.Process(target=_proceso_organizar, args=(tarea, params, cola_p, ev))
        pr.start()
        fin_ = {("final",), ("cancelado_final",), ("error",), ("prep_listo",), ("prep_error",)}

        def puente():
            while True:
                if cancelar.is_set():
                    ev.set()
                try:
                    msg = cola_p.get(timeout=0.3)
                except queue.Empty:
                    if not pr.is_alive():
                        org_cola.put(((("prep_error",) if tarea == "preparar" else ("error",)),
                                      "El proceso se cerró de forma inesperada."))
                        break
                    continue
                org_cola.put(msg)
                if msg[0] in fin_:
                    break
            pr.join(timeout=10)

        threading.Thread(target=puente, daemon=True).start()

    def org_tmp():
        import tempfile
        if not org.get("tmp"):
            org["tmp"] = tempfile.mkdtemp(prefix="PdFOL_organizar_")
            import atexit
            atexit.register(shutil.rmtree, org["tmp"], True)
        return org["tmp"]

    def org_preparar(rutas, al_terminar):
        """Aplana y comprime cada PDF en una carpeta temporal (el original no se toca)."""
        import tempfile
        if not org.get("tmp"):
            org["tmp"] = tempfile.mkdtemp(prefix="PdFOL_organizar_")
            import atexit
            atexit.register(shutil.rmtree, org["tmp"], True)
        dpi = entero(V["dpi"], DPI_DEFECTO, 72)
        texto_ = V["texto"].get()
        nivel = NIVELES_UI.get(V["nivel"].get(), "equilibrada")
        cancelar.clear()
        org["preparando"] = True
        org["al_terminar"] = al_terminar
        ocupar(True)
        org_info()
        barra.set(0)

        org_lanzar("preparar", {"rutas": list(rutas), "tmp": org_tmp(), "dpi": dpi, "texto": texto_,
                                "nivel": nivel})

    def foliar_al_unir():
        """v2.4: el folio no viene prendido; se prende solo al unir PDF (o si lo prende el usuario)."""
        if not V["fol"].get():
            V["fol"].set(True)
            refrescar()
            actualizar_ejemplo()

    def org_traer(rutas, pos, preparar, nuevo):
        def cargar(pares):
            for orig, prep in pares:
                if prep != orig:
                    org["origen"][prep] = orig
            if nuevo:
                org["ruta"] = rutas[0]
                org["fuentes"] = []
                org["gen"] += 1
                org["pend"].clear()
                org["cache"].clear()
                org["lru"].clear()
                org_cargar([pares[0][1]])
            else:
                org_cargar([b_ for _, b_ in pares], agregar=True, pos=pos)
                foliar_al_unir()
                v_estado.set(f"PDF agregados: {len(pares)}. Foliar quedó activado. Ordená y presioná «Procesar».")

        if nuevo:
            org["ruta"] = rutas[0]
        if preparar:
            org_preparar(rutas, lambda listos: cargar([(a_, b_) for a_, b_, *_ in listos]))
        else:
            cargar([(r_, r_) for r_ in rutas])

    def org_abrir():
        r_ = filedialog.askopenfilename(title="Elegí el PDF", filetypes=[("PDF", "*.pdf")])
        if not r_:
            return
        r_ = os.path.normpath(r_)

        def ok(_pos, prep):
            nuevo_archivo(r_)
            org_traer([r_], None, prep, nuevo=True)

        org_dialogo([r_], False, ok)

    def org_limpiar():
        """Quita todas las paginas para empezar otro trabajo sin cerrar el programa."""
        if app["ocupado"] or org["preparando"] or not org["orden"]:
            return
        if not messagebox.askyesno(NOMBRE, "¿Quitar todas las páginas y empezar de nuevo?\n\n"
                                           "Se cierra la pestaña de este documento. "
                                           "Los PDF originales y lo que ya guardaste no se tocan."):
            return
        if org.get("tmp"):  # copias preparadas temporales
            shutil.rmtree(org["tmp"], ignore_errors=True)
            org["tmp"] = None
        if vis["act"] is not None:
            cerrar_pestana(vis["act"], preguntar=False)
            cv.yview_moveto(0)
            org_dibujar(True)
            cv.focus_set()
            return
        org.update(fuentes=[], orden=[], sel=set(), ancla=None, pila=[], copiado=[], ruta=None, original=[],
                   origen={}, arrastre=None)
        org["gen"] += 1
        org["pend"].clear()
        org["cache"].clear()
        org["lru"].clear()
        org["fotos"].clear()
        if org.get("tmp"):  # copias preparadas temporales
            shutil.rmtree(org["tmp"], ignore_errors=True)
            org["tmp"] = None
        V["ruta"].set("")
        app.update(scores=None, salida=None, n_paginas=None, listas=set())
        v_detalle.set("")
        barra.set(0)
        v_info_doc.set("Ningún documento seleccionado.")
        v_info_apl.set("Presioná «Analizar» para detectar los planos pesados.")
        cv.yview_moveto(0)
        org_dibujar(True)
        refrescar()
        cv.focus_set()

    def org_unir():
        rs = filedialog.askopenfilenames(title="Elegí los PDF para unir", filetypes=[("PDF", "*.pdf")])
        if not rs:
            return
        rs = [os.path.normpath(x) for x in rs]
        org_dialogo(rs, True, lambda pos, prep: org_traer(rs, pos, prep, nuevo=False))

    def ayuda_organizar():
        """Los atajos de Organizar en un globo con el estilo de PdFOL (se cierra con un clic o Esc)."""
        m_ = menu_contextual()
        m_.add_titulo("Atajos de Organizar y unir")
        for t_, a_ in (("Elegir varias páginas", "Ctrl+clic / Shift"), ("Elegir sombreando", "desde un espacio vacío"),
                       ("Elegir todas", "Ctrl+A"), ("Mover páginas", "arrastrar · Ctrl+flechas"),
                       ("Copiar · Cortar · Pegar", "Ctrl+C · Ctrl+X · Ctrl+V"), ("Eliminar", "Supr"),
                       ("Deshacer · Rehacer", "Ctrl+Z · Ctrl+Y"), ("Ver la página", "doble clic · Enter"),
                       ("Todas las opciones", "clic derecho")):
            m_.add_command(label=t_, acelerador=a_)
        b_ = b_org["ayuda"]
        m_.tk_popup(b_.winfo_rootx() + b_.winfo_width() - 360, b_.winfo_rooty() + b_.winfo_height() + 4)

    def org_al_visor():
        """Organizar -> el mismo documento en el visor (en la pagina elegida)."""
        i_ = min(org["sel"]) if org["sel"] else 0
        mostrar_pagina("visor")
        raiz.after(80, lambda: vista_activa().ir(i_))

    for k_, f_ in (("abrir", org_abrir), ("unir", org_unir), ("ver", lambda: org_visor(min(org["sel"]))),
                   ("visor_v", org_al_visor),
                   ("izq", lambda: org_paso(-1)), ("der", lambda: org_paso(1)), ("mover_a", org_mover_dialogo),
                   ("rot_i", lambda: org_girar(-90)), ("rot_d", lambda: org_girar(90)),
                   ("deshacer", org_deshacer), ("rehacer", org_rehacer), ("todo", org_original),
                   ("limpiar", org_limpiar), ("ayuda", lambda: ayuda_organizar())):
        b_org[k_].configure(command=f_)
    raiz.after(300, org_recibir)

    # ================================================== VISOR (pestanas + miniaturas + documento)
    # Las paginas, las miniaturas y la busqueda corren en PROCESOS aparte (PyMuPDF no suelta el GIL con
    # planos pesados): la ventana nunca se congela. Solo se pide lo que se ve, por mosaicos si hace falta.
    from PIL import ImageTk
    import bisect
    MARGEN_V, ESPACIO_V = 18, 16
    MINI_TAM, MINI_CELDA = 112, 150
    CACHE_TROZOS, CACHE_MINI = 90, 300
    ZOOMS = ["50 %", "75 %", "100 %", "150 %", "200 %", "Ajustar ancho", "Página entera"]
    PASOS_ZOOM = [10, 25, 33, 50, 67, 75, 90, 100, 125, 150, 175, 200, 250, 300, 400, 500, 600, 800]
    PX_PT = 96 / 72  # 100 % = tamano real en pantalla
    pest = []        # pestanas abiertas (una por archivo)
    vis = {"act": None, "cache": {}, "lru": [], "mcache": {}, "mlru": [], "ult": None, "ult_mini": None,
           "mjob": None, "procs": [], "med": {}, "pedida": set(), "ver_arch": {}, "comp": False, "orgver": 0,
           "busq": None, "nbusq": 0, "res": {}, "res_pila": [], "modo_res": False, "capas": {},
           "pest_w": {}, "arr_mini": None, "arr_pest": None, "npal": 0}

    buscador = {"proc": None}

    def asegurar_buscador():
        """v2.6: el proceso de buscar (y de elegir texto) arranca recien cuando hace falta
        o unos segundos despues de abrir: asi no compite con el arranque."""
        if buscador["proc"] is None:
            try:
                pr_ = mp.Process(target=_proceso_buscar, args=(q_bus, q_sal), daemon=True)
                pr_.start()
                buscador["proc"] = pr_
                vis["procs"].append(pr_)
            except Exception:
                buscador["proc"] = False

    def iniciar_dibujantes():
        vis["procs"].extend(procs_inicio)  # ya arrancaron al principio
        raiz.after(3500, asegurar_buscador)

    def detener_dibujantes():
        for q_ in (q_pag, q_min, q_bus):
            try:
                q_.put(None)
            except Exception:
                pass
        if ocr_["p"]:
            try:
                ocr_q_ent.put(None)
                vis["procs"].append(ocr_["p"])
            except Exception:
                pass
        if org_proc["p"]:
            try:
                org_q_ent.put(None)
                vis["procs"].append(org_proc["p"])
            except Exception:
                pass
        for pr in vis["procs"]:
            try:
                pr.join(timeout=0.5)
                if pr.is_alive():
                    pr.terminate()
            except Exception:
                pass

    def soltar_archivo(ruta):
        """Los procesos sueltan el PDF (para poder guardarle los resaltados)."""
        soltar_ayuda(ruta)
        for q_ in (q_pag, q_min, q_bus):
            q_.put(("cerrar", ruta))
        org_pedidos.put(("cerrar", ruta, None, None))

    visor.grid_columnconfigure(0, weight=1)
    visor.grid_rowconfigure(1, weight=1)

    # ---------- barra general del visor (v2.4: va en la fila de las pestanas, a la derecha,
    # asi la hoja gana alto)
    # v3.0: la barra del visor queda arriba de la hoja y solo aparece cuando tiene algo
    # (busqueda, comparar o cambios sin guardar); lo demas esta en la cinta
    barra_vis = ctk.CTkFrame(visor, fg_color="transparent")

    def bv(master, texto, cmd, ancho, **kw):
        b_ = boton(master, texto, ancho=ancho, command=cmd, **kw)
        b_.configure(height=28, font=F(12))
        return b_

    b_minis = bv(barra_vis, "☰  Miniaturas", lambda: alternar_miniaturas(), 112)

    v_herr = tk.StringVar(value="Seleccionar")  # siempre arranca en Seleccionar
    seg_herr = segmentado(barra_vis, ["Seleccionar", "Mano"], v_herr, ancho=170, cmd=lambda _v: cambiar_herramienta())

    b_resaltar = bv(barra_vis, "🖍  Resaltar", lambda: alternar_resaltar(), 98)

    b_guardar_res = bv(barra_vis, "Guardar resaltados", lambda: guardar_resaltados_dialogo(), 150, primario=True)
    # busqueda: «texto»: 3 de 12  ▲ ▼  Resaltar resultados  ✕
    caja_busq = ctk.CTkFrame(barra_vis, fg_color=C["tarjeta"], corner_radius=8, border_width=1,
                             border_color=C["borde"])
    v_busq = tk.StringVar(value="")
    ctk.CTkLabel(caja_busq, textvariable=v_busq, font=F(12), text_color=C["texto"]).pack(side="left", padx=(10, 6))
    for t_b, f_b in (("▲", lambda: busq_mover(-1)), ("▼", lambda: busq_mover(1))):
        ctk.CTkButton(caja_busq, text=t_b, width=28, height=26, corner_radius=6, font=F(11),
                      fg_color=C["suave"], hover_color=C["suave_h"], text_color=C["texto"],
                      command=f_b).pack(side="left", padx=1, pady=2)
    ctk.CTkButton(caja_busq, text="Resaltar resultados", width=130, height=26, corner_radius=6, font=F(11),
                  fg_color=C["suave"], hover_color=C["suave_h"], text_color=C["texto"],
                  command=lambda: resaltar_resultados()).pack(side="left", padx=(6, 1))
    ctk.CTkButton(caja_busq, text="✕", width=26, height=26, corner_radius=13, font=F(11), fg_color="transparent",
                  hover_color=C["suave_h"], text_color=C["texto2"],
                  command=lambda: busq_cerrar()).pack(side="left", padx=(2, 4))

    b_separar = bv(barra_vis, "Separar  ✕", lambda: separar(), 100)
    v_juntas = tk.BooleanVar(value=True)
    chk_juntas = ctk.CTkCheckBox(barra_vis, text="Desplazar juntas", variable=v_juntas, font=F(12),
                                 text_color=C["texto"], fg_color=C["acento"], hover_color=C["acento_h"],
                                 border_color=C["texto2"], checkbox_width=18, checkbox_height=18, border_width=2)

    # ---------- miniaturas (izquierda, se pueden ocultar)
    panel_min = ctk.CTkFrame(col_izq, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"],
                             width=ANCHO_IZQ)
    panel_min.grid(row=0, column=0, rowspan=2, sticky="nsew")
    panel_min.grid_rowconfigure(0, weight=1)
    cvm = tk.Canvas(panel_min, width=ANCHO_IZQ - 30, highlightthickness=0, bd=0, takefocus=1)
    cvm.grid(row=0, column=0, sticky="ns", padx=(6, 0), pady=8)
    sbm = Desliz(panel_min, command=lambda *a: (cvm.yview(*a), mini_pedir_dibujo()),
                           button_color=C["suave_h"], button_hover_color=C["borde"])
    sbm.grid(row=0, column=1, sticky="ns", padx=(0, 4), pady=8)
    cvm.configure(yscrollcommand=sbm.set, yscrollincrement=MINI_CELDA // 3)

    # ---------- area de documentos (una vista, o dos para comparar) y panel de herramienta
    area_doc = ctk.CTkFrame(visor, fg_color="transparent")
    area_doc.grid(row=1, column=0, sticky="nsew", padx=(8, 14), pady=(10, 12))
    area_doc.grid_rowconfigure(0, weight=1)
    area_doc.grid_columnconfigure(0, weight=1, uniform="vistas")
    area_doc.grid_columnconfigure(1, weight=0, uniform="")

    # ---------- v3.0: barra de abajo (como Nitro): estado, paginas, modo de vista y zoom
    barra_inf = ctk.CTkFrame(visor, fg_color=C["tarjeta"], corner_radius=0, height=38)
    # v3.2: ya no se muestra (como en Adobe, paginas y zoom van en la barra de arriba)
    barra_inf.grid_columnconfigure(0, weight=1)
    ctk.CTkFrame(barra_inf, height=1, fg_color=C["borde"], corner_radius=0).place(relx=0, rely=0, relwidth=1)
    v_estado_corto = tk.StringVar(value="")

    def _estado_corto(*_):
        t_ = " ".join(v_estado.get().split())
        v_estado_corto.set(t_ if len(t_) <= 120 else t_[:118] + "…")
    v_estado.trace_add("write", _estado_corto)
    ctk.CTkLabel(barra_inf, textvariable=v_estado_corto, font=F(11), text_color=C["texto2"], anchor="w").grid(
        row=0, column=0, sticky="ew", padx=(14, 8), pady=5)
    caja_inf = ctk.CTkFrame(barra_inf, fg_color="transparent")
    caja_inf.grid(row=0, column=1, sticky="e", padx=(0, 10), pady=4)

    def b_inf(master, txt, cmd, ancho=28, img=None):
        b_ = ctk.CTkButton(master, text=txt, width=ancho, height=26, corner_radius=6, font=F(12), image=img,
                           fg_color=C["suave"], hover_color=C["suave_h"], text_color=C["texto"], command=cmd)
        return b_

    def img_inf(clave):
        return ctk.CTkImage(_icono(clave, C["suave"][0], 54, glifo=_hex(C["acento"][0])),
                            _icono(clave, C["suave"][1], 54, glifo=_hex(C["acento"][1])), size=(18, 18))

    v_pag_inf, v_tot_inf = tk.StringVar(value=""), tk.StringVar(value="")
    for txt_, f_ in (("«", lambda: ir_inf(0)), ("‹", lambda: ir_inf("ant"))):
        b_inf(caja_inf, txt_, f_).pack(side="left", padx=1)
    e_pag_inf = entrada(caja_inf, v_pag_inf, 44, justify="center")
    e_pag_inf.configure(height=26)
    e_pag_inf.pack(side="left", padx=(4, 4))
    e_pag_inf.bind("<Return>", lambda e: ir_inf("txt"))
    ctk.CTkLabel(caja_inf, textvariable=v_tot_inf, font=F(12), text_color=C["texto2"]).pack(side="left", padx=(0, 4))
    for txt_, f_ in (("›", lambda: ir_inf("sig")), ("»", lambda: ir_inf(-1))):
        b_inf(caja_inf, txt_, f_).pack(side="left", padx=1)
    ctk.CTkFrame(caja_inf, width=1, height=20, fg_color=C["borde"]).pack(side="left", padx=10)
    b_modos = {}
    for m_ in ("una", "continua", "dos"):
        b_modos[m_] = b_inf(caja_inf, "", lambda m__=m_: modo_vista(m__), 30, img_inf(m_))
        b_modos[m_].pack(side="left", padx=1)
    b_inf(caja_inf, "", lambda: girar_vista(90), 30, img_inf("girar_der")).pack(side="left", padx=(6, 1))
    ctk.CTkFrame(caja_inf, width=1, height=20, fg_color=C["borde"]).pack(side="left", padx=10)
    b_inf(caja_inf, "−", lambda: (vista_activa() and vista_activa().zoom_paso(-1))).pack(side="left", padx=1)
    zoom_inf = {"arrastrando": False}

    def _slider(pos):
        v_ = vista_activa()
        if v_ and v_.t:
            v_.poner_zoom(round(10 * 80 ** float(pos)))
    s_zoom = ctk.CTkSlider(caja_inf, from_=0, to=1, width=120, height=14, command=_slider,
                           button_color=C["acento"], button_hover_color=C["acento_h"], progress_color=C["acento"],
                           fg_color=C["suave"])
    s_zoom.pack(side="left", padx=4)
    s_zoom.bind("<ButtonPress-1>", lambda e: zoom_inf.update(arrastrando=True), add="+")
    s_zoom.bind("<ButtonRelease-1>", lambda e: zoom_inf.update(arrastrando=False), add="+")
    b_inf(caja_inf, "+", lambda: (vista_activa() and vista_activa().zoom_paso(1))).pack(side="left", padx=1)
    v_pct_inf = tk.StringVar(value="")
    ctk.CTkLabel(caja_inf, textvariable=v_pct_inf, font=F(12, "bold"), text_color=C["texto"], width=52).pack(
        side="left", padx=(4, 0))

    def ir_inf(a_):
        v_ = vista_activa()
        if not v_ or not v_.lay:
            return
        n_ = len(v_.lay["pags"])
        paso_ = 2 if (v_.t or {}).get("modo_vista") == "dos" else 1
        if a_ in ("txt", "bar"):
            try:
                v_.ir(int((v_pag_bar if a_ == "bar" else v_pag_inf).get().strip()) - 1)
            except ValueError:
                pass
            v_.cv.focus_set()
        elif a_ == "ant":
            v_.ir(v_.pag - paso_)
        elif a_ == "sig":
            v_.ir(v_.pag + paso_)
        else:
            v_.ir(n_ - 1 if a_ == -1 else 0)

    # ---------- v3.0: inicio sin documento (abrir, recientes y herramientas a un clic)
    inicio_f = ctk.CTkFrame(area_doc, fg_color=C["fondo"], corner_radius=0)
    inicio_caja = ctk.CTkFrame(inicio_f, fg_color="transparent")
    inicio_caja.place(relx=0.5, rely=0.08, anchor="n")
    ctk.CTkLabel(inicio_caja, text="Inicio", font=F(24, "bold"), text_color=C["texto"], anchor="w").pack(fill="x")
    ctk.CTkLabel(inicio_caja, text="Abrí un PDF, elegí uno reciente o empezá con una herramienta.", font=F(13),
                 text_color=C["texto2"], anchor="w").pack(fill="x", pady=(2, 16))
    fila_ini = ctk.CTkFrame(inicio_caja, fg_color="transparent")
    fila_ini.pack(fill="x")
    ctk.CTkButton(fila_ini, text="   Abrir PDF   ·   Ctrl+O", font=F(15, "bold"), width=330,
                  height=86, corner_radius=12, anchor="w", fg_color=C["acento"], hover_color=C["acento_h"],
                  text_color="#FFFFFF", image=ctk.CTkImage(_icono("abrir", "#2563EB", 40 * 3), size=(40, 40)),
                  command=lambda: abrir_archivos()).pack(side="left", padx=(0, 12))
    for c_ini, t_ini, f_ini in (("organizar", "Unir PDFs", lambda: cinta_unir()),
                                ("comprimir", "Comprimir", lambda: cinta_panel("comprimir")),
                                ("foliar", "Foliar", lambda: cinta_panel("foliar"))):
        ctk.CTkButton(fila_ini, text=t_ini, font=F(13), width=140, height=86, corner_radius=12, compound="top",
                      fg_color=C["tarjeta"], hover_color=C["suave_h"], text_color=C["texto"], border_width=1,
                      border_color=C["borde"], image=ctk.CTkImage(_icono(c_ini, COLOR_ICONO[c_ini], 30 * 3), size=(30, 30)),
                      command=f_ini).pack(side="left", padx=(0, 10))
    ctk.CTkLabel(inicio_caja, text="Recientes", font=F(14, "bold"), text_color=C["texto"], anchor="w").pack(
        fill="x", pady=(24, 6))
    lista_rec = ctk.CTkFrame(inicio_caja, fg_color=C["tarjeta"], corner_radius=12, border_width=1,
                             border_color=C["borde"], width=820)
    lista_rec.pack(fill="x")

    def recordar_reciente(r_):
        rec = [x for x in almacen.datos.get("recientes", []) if os.path.normcase(x) != os.path.normcase(r_)]
        almacen.datos["recientes"] = ([r_] + rec)[:12]
        almacen.guardar()

    def dibujar_inicio():
        for w_ in lista_rec.winfo_children():
            w_.destroy()
        rec = [x for x in almacen.datos.get("recientes", []) if os.path.isfile(x)][:8]
        if not rec:
            ctk.CTkLabel(lista_rec, text="Todavía no abriste ningún PDF con PdFOL.", font=F(12),
                         text_color=C["texto2"], anchor="w").pack(fill="x", padx=18, pady=16)
            return
        for r_ in rec:
            try:
                st_ = os.stat(r_)
                fecha = time.strftime("%d/%m/%Y %H:%M", time.localtime(st_.st_mtime))
                tam_ = f"{st_.st_size / 1048576:.1f} MB" if st_.st_size > 1048576 else f"{st_.st_size // 1024} KB"
            except Exception:
                fecha, tam_ = "", ""
            fila_ = ctk.CTkFrame(lista_rec, fg_color="transparent", corner_radius=8, height=50, cursor="hand2")
            fila_.pack(fill="x", padx=6, pady=(4, 0))
            ico_ = ctk.CTkLabel(fila_, text="", image=ctk.CTkImage(_icono("documento", COLOR_ICONO["documento"], 72),
                                                                    size=(24, 24)))
            ico_.pack(side="left", padx=(10, 12), pady=8)
            txts_ = ctk.CTkFrame(fila_, fg_color="transparent")
            txts_.pack(side="left", fill="x", expand=True)
            l1_ = ctk.CTkLabel(txts_, text=os.path.basename(r_), font=F(12, "bold"), text_color=C["texto"],
                               anchor="w", height=18)
            l1_.pack(fill="x")
            l2_ = ctk.CTkLabel(txts_, text=os.path.dirname(r_), font=F(11), text_color=C["texto2"], anchor="w",
                               height=16)
            l2_.pack(fill="x")
            l3_ = ctk.CTkLabel(fila_, text=f"{fecha}    {tam_}", font=F(11), text_color=C["texto2"])
            l3_.pack(side="right", padx=14)
            for w_ in (fila_, ico_, txts_, l1_, l2_, l3_):
                w_.bind("<Button-1>", lambda e, r__=r_: abrir_pestana(r__))
                w_.bind("<Enter>", lambda e, f__=fila_: f__.configure(fg_color=C["suave"]))
                w_.bind("<Leave>", lambda e, f__=fila_: f__.configure(fg_color="transparent"))
        ctk.CTkFrame(lista_rec, height=6, fg_color="transparent").pack()

    def mostrar_inicio():
        """v3.2: «Inicio» (o sin documento) y «Herramientas» se ven sobre la hoja, como en Adobe."""
        en_visor = app["pagina"] == "visor" and not vis["comp"]
        ver_ini = en_visor and (app["vista_top"] == "inicio" or (not pest and app["vista_top"] != "herr"))
        ver_herr = en_visor and app["vista_top"] == "herr"
        if ver_ini:
            if not inicio_f.winfo_ismapped():
                dibujar_inicio()
                inicio_f.place(relx=0, rely=0, relwidth=1, relheight=1)
            inicio_f.lift()
        elif inicio_f.winfo_ismapped():
            inicio_f.place_forget()
        if ver_herr:
            if not herr_w.winfo_ismapped():
                herr_w.place(relx=0, rely=0, relwidth=1, relheight=1)
            herr_w.lift()
            raiz.after_idle(dibujar_herr)
        elif herr_w.winfo_ismapped():
            herr_w.place_forget()

    # ---------- v3.2: «Herramientas»: todas las herramientas en tarjetas (como Adobe)
    # v4.0: las tarjetas se DIBUJAN en un solo lienzo (antes eran ~140 controles armados al iniciar)
    herr_w = tk.Frame(area_doc, bd=0, highlightthickness=0)
    herr_cv = tk.Canvas(herr_w, highlightthickness=0, bd=0)
    herr_sb = Desliz(herr_w, command=herr_cv.yview, button_color=C["suave_h"],
                               button_hover_color=C["borde"])
    herr_sb.pack(side="right", fill="y")
    herr_cv.pack(side="left", fill="both", expand=True)
    herr_cv.configure(yscrollcommand=herr_sb.set)
    herr_est = {"sobre": None, "fotos": {}}
    HERRAMIENTAS = [
        ("agregar", "Agregar texto", "Escribir texto nuevo sobre la hoja", lambda: cinta_texto("Agregar")),
        ("cambiar", "Cambiar texto", "Reemplazar texto del PDF (párrafo o renglón)", lambda: cinta_texto("Cambiar")),
        ("firmar", "Firmar y sellar", "Firmas y sellos desde una imagen", lambda: cinta_panel("firmar")),
        ("resaltar", "Resaltar", "Marcar texto o zonas", lambda: alternar_resaltar()),
        ("organizar", "Organizar y unir", "Ordenar, girar, quitar y unir páginas", lambda: cinta_pagina("organizar")),
        ("comparar", "Comparar", "Dos PDF lado a lado", lambda: boton_comparar()),
        ("documento", "Documento", "Propiedades, páginas y archivo", lambda: cinta_pagina("documento")),
        ("aplanar", "Aplanar", "Planos livianos para imprimir y ver", lambda: cinta_panel("aplanar")),
        ("foliar", "Foliar", "Numerar las hojas", lambda: cinta_panel("foliar")),
        ("comprimir", "Comprimir", "Bajar el peso del PDF", lambda: cinta_panel("comprimir")),
        ("imprimir", "Imprimir", "Imprimir con las opciones de PdFOL", lambda: abrir_imprimir()),
        ("perfiles", "Perfiles", "Guardar y usar tus ajustes", lambda: cinta_pagina("perfiles")),
        ("apariencia", "Apariencia", "Claro, oscuro y colores", lambda: cinta_pagina("apariencia")),
    ]

    def usar_herramienta(f_):
        app["vista_top"] = None
        mostrar_inicio()
        dibujar_superior()
        f_()

    def _redondeado(cv_, x0, y0, x1, y1, r, **kw):
        pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1, x1 - r, y1, x0 + r, y1, x0, y1,
               x0, y1 - r, x0, y0 + r, x0, y0]
        return cv_.create_polygon(pts, smooth=True, **kw)

    def herr_geo():
        cw_, ch_, gap = px(250), px(74), px(12)
        cols = max(1, min(3, (herr_cv.winfo_width() - px(60) + gap) // (cw_ + gap)))
        x0 = max(px(30), (herr_cv.winfo_width() - cols * cw_ - (cols - 1) * gap) // 2)
        return cw_, ch_, gap, cols, x0, px(80)

    def dibujar_herr(*_):
        if not herr_w.winfo_ismapped():
            return
        cv_ = herr_cv
        fondo = col("fondo")
        herr_w.configure(bg=fondo)
        cv_.configure(bg=fondo)
        cv_.delete("all")
        cw_, ch_, gap, cols, x0, y0 = herr_geo()
        cv_.create_text(x0 + 4, px(44), text="Herramientas", anchor="w", fill=col("texto"), font=(FAM, 18, "bold"))
        for k_h, (cl_, tit_, desc_, f_) in enumerate(HERRAMIENTAS):
            x = x0 + (k_h % cols) * (cw_ + gap)
            y = y0 + (k_h // cols) * (ch_ + gap)
            sobre = herr_est["sobre"] == k_h
            _redondeado(cv_, x, y, x + cw_, y + ch_, px(12), fill=col("tarjeta"),
                        outline=col("acento") if sobre else col("borde"), width=2 if sobre else 1,
                        tags=("tarj", f"h{k_h}"))
            kf = (cl_, px(34))
            ft = herr_est["fotos"].get(kf)
            if ft is None:
                ft = herr_est["fotos"][kf] = foto_tk(_icono(cl_, COLOR_ICONO.get(cl_, "#64748B"), px(34)))
            cv_.create_image(x + px(14) + px(17), y + ch_ / 2, image=ft, tags=("tarj", f"h{k_h}"))
            cv_.create_text(x + px(60), y + px(22), text=tit_, anchor="w", fill=col("texto"),
                            font=(FAM, 10, "bold"), tags=("tarj", f"h{k_h}"))
            cv_.create_text(x + px(60), y + px(46), text=desc_, anchor="w", fill=col("texto2"), font=(FAM, 8),
                            width=cw_ - px(72), tags=("tarj", f"h{k_h}"))
        filas = (len(HERRAMIENTAS) + cols - 1) // cols
        cv_.configure(scrollregion=(0, 0, cv_.winfo_width(), y0 + filas * (ch_ + gap) + px(20)))

    def herr_indice(ev):
        cw_, ch_, gap, cols, x0, y0 = herr_geo()
        x, y = herr_cv.canvasx(ev.x) - x0, herr_cv.canvasy(ev.y) - y0
        if x < 0 or y < 0:
            return None
        c_, f_ = int(x // (cw_ + gap)), int(y // (ch_ + gap))
        if c_ >= cols or x - c_ * (cw_ + gap) > cw_ or y - f_ * (ch_ + gap) > ch_:
            return None
        k_ = f_ * cols + c_
        return k_ if k_ < len(HERRAMIENTAS) else None

    def herr_mover(ev):
        k_ = herr_indice(ev)
        if k_ != herr_est["sobre"]:
            herr_est["sobre"] = k_
            herr_cv.configure(cursor="hand2" if k_ is not None else "")
            dibujar_herr()

    def herr_clic(ev):
        k_ = herr_indice(ev)
        if k_ is not None:
            herr_est["sobre"] = None
            usar_herramienta(HERRAMIENTAS[k_][3])

    herr_cv.bind("<Motion>", herr_mover)
    herr_cv.bind("<Leave>", lambda e: (herr_est.update(sobre=None), dibujar_herr()))
    herr_cv.bind("<Button-1>", herr_clic)
    herr_cv.bind("<Configure>", lambda e: raiz.after_idle(dibujar_herr))
    for ev_ in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
        herr_cv.bind(ev_, lambda e: herr_cv.yview_scroll(-1 if (getattr(e, "delta", 0) > 0 or
                                                                 getattr(e, "num", 0) == 4) else 1, "units"))

    # ---------- v3.2: riel de herramientas a la derecha (iconos de color, como Adobe)
    RIEL_DER = [("agregar", "Agregar texto", lambda: cinta_texto("Agregar"), "texto:Agregar"),
                ("cambiar", "Cambiar texto del PDF", lambda: cinta_texto("Cambiar"), "texto:Cambiar"),
                ("firmar", "Firmar y sellar", lambda: cinta_panel("firmar"), "firmar"),
                ("resaltar", "Resaltar", lambda: alternar_resaltar(), "resaltar"),
                None,
                ("organizar", "Organizar y unir", lambda: cinta_pagina("organizar"), "p:organizar"),
                ("comparar", "Comparar dos PDF", lambda: boton_comparar(), "comparar"),
                ("documento", "Documento", lambda: cinta_pagina("documento"), "p:documento"),
                None,
                ("aplanar", "Aplanar", lambda: cinta_panel("aplanar"), "aplanar"),
                ("foliar", "Foliar", lambda: cinta_panel("foliar"), "foliar"),
                ("comprimir", "Comprimir", lambda: cinta_panel("comprimir"), "comprimir"),
                ("imprimir", "Imprimir", lambda: abrir_imprimir(), None),
                ("perfiles", "Perfiles", lambda: cinta_pagina("perfiles"), "p:perfiles"),
                None,
                ("apariencia", "Apariencia", lambda: cinta_pagina("apariencia"), "p:apariencia"),
                ("herramientas", "Todas las herramientas", lambda: ir_top("herr"), "top:herr")]
    riel_der = tk.Canvas(cuerpo, width=px(44), highlightthickness=0, bd=0, cursor="hand2")
    riel_der.grid(row=0, column=4, sticky="ns")
    iconos_riel = {}

    def riel_elegido(clave_):
        if not clave_:
            return False
        if clave_.startswith("p:"):
            return app["pagina"] == clave_[2:]
        if clave_.startswith("top:"):
            return app["vista_top"] == clave_[4:]
        if clave_.startswith("texto:"):
            try:
                return app.get("panel") == "texto" and v_tmodo.get() == clave_[6:]
            except Exception:
                return False
        if clave_ == "resaltar":
            return bool(vis["modo_res"])
        if clave_ == "comparar":
            return bool(vis["comp"])
        return app["pagina"] == "visor" and app.get("panel") == clave_

    def dibujar_riel_der(*_):
        riel_der.delete("all")
        riel_der.configure(bg=col("tarjeta"))
        h_ = riel_der.winfo_height()
        riel_der.create_line(0, 0, 0, h_, fill=col("borde"))
        y = px(10)
        app["riel_acc"], app["riel_ayuda"] = {}, {}
        for k_, it_ in enumerate(RIEL_DER):
            if it_ is None:
                riel_der.create_line(px(10), y + px(4), px(34), y + px(4), fill=col("borde"))
                y += px(10)
                continue
            cl_, ayuda_, f_, est_ = it_
            if riel_elegido(est_):
                riel_der.create_rectangle(px(4), y, px(40), y + px(36), fill=col("lat_sel"), outline="")
            kk = (cl_, modo_oscuro())
            if kk not in iconos_riel:
                iconos_riel[kk] = foto_tk(_icono(cl_, COLOR_ICONO.get(cl_, "#64748B"), px(24)))
            riel_der.create_image(px(22), y + px(18), image=iconos_riel[kk], tags=("item", f"r:{k_}"))
            riel_der.create_rectangle(px(4), y, px(40), y + px(36), outline="", fill="", tags=("item", f"r:{k_}"))
            app["riel_acc"][str(k_)] = f_
            app["riel_ayuda"][str(k_)] = ayuda_
            y += px(40)

    def click_riel(ev):
        ayuda_esconder()
        for it in reversed(riel_der.find_overlapping(ev.x, ev.y, ev.x, ev.y)):
            for t in riel_der.gettags(it):
                if t.startswith("r:"):
                    f_ = app["riel_acc"].get(t[2:])
                    if f_:
                        if app["vista_top"] and "herr" not in str(t):
                            app["vista_top"] = None
                            mostrar_inicio()
                            dibujar_superior()
                        f_()
                    raiz.after(20, dibujar_riel_der)
                    return

    riel_der.bind("<Configure>", dibujar_riel_der)
    riel_der.bind("<Button-1>", click_riel)
    riel_der.bind("<Motion>", lambda e: ayuda_mover(e, riel_der, lambda: app.get("riel_ayuda", {})))
    riel_der.bind("<Leave>", ayuda_esconder)

    # ---------- v3.2: los mensajes aparecen un rato abajo a la izquierda de la hoja (sin barra fija)
    aviso_lbl = ctk.CTkLabel(area_doc, text="", font=F(12), fg_color=C["tarjeta"], text_color=C["texto"],
                             corner_radius=8, height=30, anchor="w", wraplength=700, justify="left")
    aviso_job = {"id": None}

    def mostrar_aviso(*_):
        t_ = " ".join(v_estado.get().split())
        if "«Analizar»" in t_ and app.get("panel") not in ("aplanar", "foliar", "comprimir"):
            t_ = ""  # mensaje de Aplanar: solo con ese panel abierto
        if aviso_job["id"]:
            raiz.after_cancel(aviso_job["id"])
            aviso_job["id"] = None
        if not t_ or app["pagina"] != "visor":
            aviso_lbl.place_forget()
            return
        aviso_lbl.configure(text=f"  {t_ if len(t_) <= 220 else t_[:218] + '…'}  ")
        aviso_lbl.place(x=16, rely=1.0, y=-14, anchor="sw")
        aviso_lbl.lift()
        aviso_job["id"] = raiz.after(7000, lambda: aviso_lbl.place_forget())
    v_estado.trace_add("write", mostrar_aviso)
    aviso_lbl.bind("<Button-1>", lambda e: aviso_lbl.place_forget())

    def menu_desde(widget_x, items_):
        m_ = tk.Menu(raiz, tearoff=0, font=(FAM, 10))
        for txt_, f_ in items_:
            if txt_ == "-":
                m_.add_separator()
            else:
                m_.add_command(label=txt_, command=f_)
        try:
            m_.tk_popup(widget_x[0], widget_x[1])
        finally:
            m_.grab_release()

    def _pos_cinta(id_):
        for it in cinta.find_all():
            if "b:" + id_ in cinta.gettags(it):
                x0, y0, x1, y1 = cinta.bbox(it)
                return cinta.winfo_rootx() + x0, cinta.winfo_rooty() + y1 + 2
        return raiz.winfo_pointerx(), raiz.winfo_pointery()

    def menu_zoom():
        v_ = vista_activa()
        if not v_ or not v_.t:
            return
        menu_desde(_pos_cinta("zoom_menu"), [("Ajustar al ancho", lambda: zoom_cinta("Ajustar ancho")),
                                             ("Página entera", lambda: zoom_cinta("Página entera")), ("-", None)] +
                   [(f"{p_} %", lambda p__=p_: v_.poner_zoom(p__)) for p_ in (50, 75, 100, 125, 150, 200, 300, 400)])

    def menu_ajuste():
        menu_desde(_pos_cinta("ajuste"), [("Ajustar al ancho", lambda: zoom_cinta("Ajustar ancho")),
                                          ("Página entera", lambda: zoom_cinta("Página entera"))])

    def menu_modo():
        menu_desde(_pos_cinta("modo"), [("Una página", lambda: modo_vista("una")),
                                        ("Continua", lambda: modo_vista("continua")),
                                        ("Dos páginas", lambda: modo_vista("dos")),
                                        ("Miniaturas (se agrandan con el zoom)", lambda: modo_vista("mosaico")),
                                        ("-", None),
                                        ("Hoja impresa", lambda: V["girar_prev"].set(not V["girar_prev"].get())),
                                        ("Miniaturas", lambda: alternar_miniaturas()),
                                        ("Marcadores", lambda: alternar_marcadores())])

    def pest_activa():
        i = vis["act"]
        return pest[i] if i is not None and 0 <= i < len(pest) else None

    def org_de(t_):
        return org if t_ is pest_activa() else (t_.get("org") or {})

    def version_de(t_):
        return vis["orgver"] if t_ is pest_activa() else t_.get("orgver", 0)

    def paginas_de(t_):
        """Paginas que muestra la pestana, en el orden organizado: [(ruta, pagina, giro)]."""
        o_ = org_de(t_)
        if o_.get("orden"):
            fs = o_["fuentes"]
            return [(fs[f_], p_, r_) for f_, p_, r_ in o_["orden"]]
        med = vis["med"].get(t_["ruta"])
        return [(t_["ruta"], i, 0) for i in range(len(med))] if med else []

    def medidas_listas(t_):
        o_ = org_de(t_)
        rutas = set(o_.get("fuentes") or []) | {t_["ruta"]}
        falta = False
        for r_ in rutas:
            if r_ not in vis["med"] and not vis.get("render_listo"):
                try:  # v3.0: los tamanos los mide la ventana (los procesos todavia arrancan)
                    d_ = _abrir_cache(ayuda["docs"], ayuda["orden"], r_, maximo=3)
                    if d_.page_count <= 1500:
                        vis["med"][r_] = [(d_[i].rect.width, d_[i].rect.height) for i in range(d_.page_count)]
                except Exception:
                    pass
            if r_ not in vis["med"]:
                falta = True
                if r_ not in vis["pedida"]:
                    vis["pedida"].add(r_)
                    q_pag.put(("medidas", r_))
        return not falta

    def dims_vista(med_wh, rot, parar):
        w_, h_ = med_wh
        if rot % 180:
            w_, h_ = h_, w_
        if parar and w_ > h_ * 1.001:
            w_, h_ = h_, w_
        return w_, h_

    def ver_arch(ruta):
        return vis["ver_arch"].get(ruta, 0)

    def folio_de_posicion(n):
        """Funcion posicion -> (cfg, texto) del folio que le toca (si Foliar esta activo) y su firma."""
        if not V["fol"].get() or not n:
            return (lambda i: None), None
        try:
            cfg_ = cfg_folio()
        except Exception:
            return (lambda i: None), None
        ind_ = rango_folio(cfg_, n)
        if not ind_:
            return (lambda i: None), None
        pos_ = {p_: k_ for k_, p_ in enumerate(ind_)}
        tot_ = int(cfg_["inicio"]) + len(ind_) - 1
        firma = repr(sorted(cfg_.items()))

        def f_(i):
            k_ = pos_.get(i)
            return None if k_ is None else (cfg_, texto_folio(cfg_, int(cfg_["inicio"]) + k_, tot_))
        return f_, firma

    def capa_color(w_, h_, rgba):
        """Rectangulo de color semitransparente (resaltado) como imagen."""
        w_, h_ = max(1, int(w_)), max(1, int(h_))
        k_ = (w_, h_, rgba)
        ft = vis["capas"].get(k_)
        if ft is None:
            if len(vis["capas"]) > 300:
                vis["capas"].clear()
            ft = vis["capas"][k_] = ImageTk.PhotoImage(Image.new("RGBA", (w_, h_), rgba))
        return ft

    AMARILLO, NARANJA, RESALTE = (255, 214, 0, 95), (255, 140, 0, 130), (255, 230, 0, 120)

    # ================= una vista de documento (dos cuando se compara)
    class VistaDoc:
        def __init__(self, lado):
            self.lado, self.t, self.zoom, self.lay, self.lay_k = lado, None, "Ajustar ancho", None, None
            self.pag, self.job, self.ult, self.reanclar, self.bloq = 0, None, [], None, False
            self.marco = ctk.CTkFrame(area_doc, fg_color=C["campo"], corner_radius=12, border_width=2,
                                      border_color=C["borde"])
            self.marco.grid_columnconfigure(0, weight=1)
            self.marco.grid_rowconfigure(2, weight=1)
            # nombre del documento (solo al comparar) y barra: ◀ pagina ▶ · lupa − zoom +
            self.v_nom = tk.StringVar(value="")
            self.l_nom = ctk.CTkLabel(self.marco, textvariable=self.v_nom, font=F(12, "bold"), text_color=C["texto"],
                                      anchor="w")
            bar = self.bar = ctk.CTkFrame(self.marco, fg_color="transparent")
            bar.grid(row=0, column=0, columnspan=2, sticky="ew", padx=8, pady=(6, 2))
            bar.grid_remove()  # v3.0: va abajo, en la barra general (se ve solo al comparar)
            bar.grid_columnconfigure(4, weight=1)
            self.v_pag, self.v_tot = tk.StringVar(), tk.StringVar()
            self.b_ant = bv(bar, "◀", lambda: self.ir(self.pag - 1), 34)
            self.e_pag = entrada(bar, self.v_pag, 50, justify="center")
            self.e_pag.bind("<Return>", self._ir_txt)
            self.l_tot = ctk.CTkLabel(bar, textvariable=self.v_tot, font=F(12), text_color=C["texto2"])
            self.b_sig = bv(bar, "▶", lambda: self.ir(self.pag + 1), 34)
            self.l_lupa = ctk.CTkLabel(bar, text="🔍", font=F(13), text_color=C["texto2"])
            self.b_menos = bv(bar, "−", lambda: self.zoom_paso(-1), 34)
            self.v_zoom = tk.StringVar(value="Ajustar ancho")
            self.m_zoom = menu(bar, ZOOMS, self.v_zoom, ancho=136, cmd=lambda v_: self.poner_zoom(v_))
            self.b_mas = bv(bar, "+", lambda: self.zoom_paso(1), 34)
            self._piezas = [(self.b_ant, 0, (0, 2)), (self.e_pag, 1, (4, 4)), (self.l_tot, 2, (0, 0)),
                            (self.b_sig, 3, (6, 2)), (self.l_lupa, 5, (0, 2)), (self.b_menos, 6, (2, 2)),
                            (self.m_zoom, 7, (2, 2)), (self.b_mas, 8, (2, 0))]
            for w_, c_, px_ in self._piezas:
                w_.grid(row=0, column=c_, padx=px_)
            self._angosta = False
            self.marco.bind("<Configure>", self._ancho, add="+")
            self.cv = tk.Canvas(self.marco, highlightthickness=0, bd=0, takefocus=1, yscrollincrement=24,
                                xscrollincrement=24)
            self.cv.grid(row=2, column=0, sticky="nsew", padx=(6, 0), pady=(2, 0))
            self.sbv = Desliz(self.marco, command=self._yview, button_color=C["suave_h"],
                                        button_hover_color=C["borde"])
            self.sbv.grid(row=2, column=1, sticky="ns", padx=(0, 4), pady=(2, 0))
            self.sbh = Desliz(self.marco, orientation="horizontal", command=self._xview,
                                        button_color=C["suave_h"], button_hover_color=C["borde"])
            self.sbh.grid(row=3, column=0, sticky="ew", padx=(6, 0), pady=(0, 4))
            self.cv.configure(yscrollcommand=self.sbv.set, xscrollcommand=self.sbh.set)
            cv_ = self.cv
            for ev_ in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
                cv_.bind(ev_, self._rueda)
            for ev_ in ("<Shift-MouseWheel>", "<Shift-Button-4>", "<Shift-Button-5>"):
                cv_.bind(ev_, lambda e: self._rueda(e, horizontal=True))
            for ev_ in ("<Control-MouseWheel>", "<Control-Button-4>", "<Control-Button-5>"):
                cv_.bind(ev_, self._rueda_zoom)
            cv_.bind("<ButtonPress-1>", self._press)
            cv_.bind("<B1-Motion>", self._motion)
            cv_.bind("<ButtonRelease-1>", self._release)
            cv_.bind("<Button-3>", self._menu)
            cv_.bind("<Motion>", self._mover_libre)
            cv_.bind("<Double-Button-1>", self._doble_clic)
            cv_.bind("<Triple-Button-1>", lambda e: self._doble_clic(e, renglon=True))
            # boton del medio: siempre desplaza
            cv_.bind("<ButtonPress-2>", lambda e: (self.cv.scan_mark(e.x, e.y), self.cv.configure(cursor="fleur")))
            cv_.bind("<B2-Motion>", lambda e: (self.cv.scan_dragto(e.x, e.y, gain=1), self.movido()))
            cv_.bind("<ButtonRelease-2>", lambda e: self.cv.configure(cursor=cursor_herramienta()))
            cv_.bind("<Return>", lambda e: self.cerrar_poligono() if getattr(self, "_poly", None) else None)
            cv_.bind("<Configure>", lambda e: self.pedir())
            cv_.bind("<Key>", self._teclas)
            self.marco.bind("<Button-1>", lambda e: self.activar())

        def _ancho(self, ev):
            """Vista angosta (comparando con el panel abierto): se ocultan ◀ ▶ y la lupa."""
            angosta = ev.width < 430
            if angosta != self._angosta:
                self._angosta = angosta
                for w_ in (self.b_ant, self.b_sig, self.l_lupa):
                    if angosta:
                        w_.grid_remove()
                    else:
                        w_.grid()
                self.m_zoom.configure(width=92 if angosta else 136)

        # ---- desplazamiento
        def _yview(self, *a):
            self.cv.yview(*a)
            self.movido()

        def _xview(self, *a):
            self.cv.xview(*a)
            self.pedir()

        def _rueda(self, ev, horizontal=False):
            if getattr(ev, "num", 0) == 4 or getattr(ev, "delta", 0) > 0:
                d = -1
            else:
                d = 1
            paso = max(1, abs(int(getattr(ev, "delta", 120) / 120))) if getattr(ev, "delta", 0) else 1
            if horizontal:
                self.cv.xview_scroll(d * paso * 3, "units")
                self.pedir()
            elif (self.t and self.t.get("modo_vista") == "una" and self.lay
                  and self.lay["hs"][min(self.pag, len(self.lay["hs"]) - 1)] <= self.cv.winfo_height() + 2):
                self.ir(self.pag + d)  # v3.0: una pagina por vez (si la hoja entera entra en la pantalla)
            else:
                self.cv.yview_scroll(d * paso * 3, "units")
                self.movido()
            return "break"

        def _rueda_zoom(self, ev):
            arriba = getattr(ev, "num", 0) == 4 or getattr(ev, "delta", 0) > 0
            self.zoom_paso(1 if arriba else -1, ancla=(ev.x, ev.y))
            return "break"

        def movido(self):
            self.pedir()
            sincronizar(self)

        def pedir(self, *_):
            if self.job is None:
                self.job = raiz.after(12, self.dibujar)

        # ---- geometria
        def layout(self):
            t_ = self.t
            if not t_ or not medidas_listas(t_):
                return None
            pags = paginas_de(t_)
            if not pags:
                return None
            W, H = max(self.cv.winfo_width(), 200), max(self.cv.winfo_height(), 150)
            parar = bool(V["girar_prev"].get())
            giro = t_.get("giro", 0)  # v3.0: girar la vista (no cambia el PDF)
            dos = t_.get("modo_vista") == "dos"
            mosaico = t_.get("modo_vista") == "mosaico"  # v3.6: miniaturas en filas (se agrandan con el zoom)
            pend = giros_pendientes()  # v3.3: paginas giradas que se guardan en el PDF
            if giro or pend:
                pags = [(r_, p_, (g_ + giro + pend.get((r_, p_), 0)) % 360) for r_, p_, g_ in pags]
            k_ = (W, H, parar, self.zoom, version_de(t_), len(pags), t_["id"], giro, dos, tuple(sorted(pend.items())),
                  vis.get("med_ver", 0), mosaico, getattr(self, "tam_mini", 0))
            if k_ == self.lay_k:
                return self.lay
            if self.lay is not None and self.reanclar is None:
                self.reanclar = self.posicion()
            disp_w, disp_h = max(120, W - 40), max(120, H - 2 * MARGEN_V)
            if dos:  # dos paginas lado a lado: cada una tiene la mitad del ancho
                disp_w = max(60, (disp_w - ESPACIO_V) / 2)
            ys, hs, ws, zs, dims = [], [], [], [], []
            y = MARGEN_V
            for ruta, pag, rot in pags:
                med = vis["med"][ruta]
                w0, h0 = med[pag] if pag < len(med) else (612, 792)
                vw, vh = dims_vista((w0, h0), rot, parar)
                if mosaico and self.zoom not in ("Ajustar ancho", "Página entera") and not isinstance(self.zoom, (int, float)):
                    tm_ = getattr(self, "tam_mini", px(170))  # todas del mismo tamano (planos y carta)
                    z = min(tm_ / max(vw, 1), tm_ * 1.414 / max(vh, 1))
                elif self.zoom == "Ajustar ancho":
                    z = disp_w / max(vw, 1)
                elif self.zoom == "Página entera":
                    z = min(disp_w / max(vw, 1), disp_h / max(vh, 1))
                elif isinstance(self.zoom, (int, float)):
                    z = float(self.zoom) / 100 * PX_PT
                else:
                    z = disp_w / max(vw, 1)
                dw, dh = max(8, int(round(vw * z))), max(8, int(round(vh * z)))
                hs.append(dh)
                ws.append(dw)
                zs.append(z)
                dims.append((w0, h0))
            if dos:
                filas = [list(range(k_i, min(k_i + 2, len(ws)))) for k_i in range(0, len(ws), 2)]
            elif mosaico:  # tantas por fila como entren
                filas, fila_, ancho_ = [], [], 0
                for k_i in range(len(ws)):
                    if fila_ and ancho_ + ESPACIO_V + ws[k_i] > disp_w:
                        filas.append(fila_)
                        fila_, ancho_ = [], 0
                    ancho_ += (ESPACIO_V if fila_ else 0) + ws[k_i]
                    fila_.append(k_i)
                if fila_:
                    filas.append(fila_)
            else:
                filas = [[k_i] for k_i in range(len(ws))]
            ys = [0] * len(ws)
            anchos_f = []
            for fila in filas:
                for k_i in fila:
                    ys[k_i] = y
                y += max(hs[k_i] for k_i in fila) + ESPACIO_V
                anchos_f.append(sum(ws[k_i] for k_i in fila) + ESPACIO_V * (len(fila) - 1))
            cw = max(W, max(anchos_f) + 40)
            xs = [0] * len(ws)
            for fila, af in zip(filas, anchos_f):
                x_ = (cw - af) // 2
                for k_i in fila:
                    xs[k_i] = x_
                    x_ += ws[k_i] + ESPACIO_V
            self.lay = {"pags": pags, "ys": ys, "hs": hs, "ws": ws, "xs": xs, "zs": zs, "dims": dims,
                        "total": y - ESPACIO_V + MARGEN_V, "cw": cw, "parar": parar}
            self.lay_k = k_
            return self.lay

        def pagina_en(self, y, x=None):
            lay = self.lay
            if not lay:
                return 0
            ys = lay["ys"]
            i = max(0, min(len(ys) - 1, bisect.bisect_right(ys, y) - 1))
            while i > 0 and ys[i - 1] == ys[i]:  # v3.0: dos paginas por fila: la primera de la fila
                i -= 1
            if x is not None:  # la de la fila que esta bajo x
                while i + 1 < len(ys) and ys[i + 1] == ys[i] and x > lay["xs"][i] + lay["ws"][i] + ESPACIO_V / 2:
                    i += 1
            return i

        def posicion(self):
            """(pagina, fraccion dentro de la pagina) de lo que se ve arriba."""
            lay = self.lay
            if not lay:
                return (self.pag, 0.0)
            y0 = self.cv.canvasy(0)
            i = self.pagina_en(y0 + 1)
            return (i, max(0.0, (y0 - lay["ys"][i]) / max(1, lay["hs"][i] + ESPACIO_V)))

        def ir_pos(self, i, frac=0.0):
            lay = self.layout()
            if not lay:
                return
            i = max(0, min(len(lay["ys"]) - 1, i))
            y = lay["ys"][i] + frac * (lay["hs"][i] + ESPACIO_V)
            self._scroll_a(y)
            self.pag = i

        def _scroll_a(self, y=None, x=None):
            lay = self.lay
            if y is not None:
                self.cv.yview_moveto(max(0.0, y / max(1, max(lay["total"], self.cv.winfo_height()))))
            if x is not None:
                self.cv.xview_moveto(max(0.0, x / max(1, lay["cw"])))

        def ir(self, i, arriba=True):
            lay = self.layout()
            if not lay:
                return
            i = max(0, min(len(lay["ys"]) - 1, int(i)))
            self.cv.configure(scrollregion=(0, 0, lay["cw"], max(lay["total"], self.cv.winfo_height())))
            self._scroll_a(lay["ys"][i] - 8)
            self.pag = i
            self.dibujar()
            if self.es_activa():
                mini_ver(i)
            sincronizar(self)

        def ver_rect(self, i, rect):
            """Lleva a la vista el rectangulo (coordenadas de la pagina) de la pagina i."""
            lay = self.layout()
            if not lay:
                return
            ruta, pag, rot = lay["pags"][i]
            w0, h0 = lay["dims"][i]
            M = matriz_vista(w0, h0, lay["zs"][i], rot, lay["parar"])
            r_ = fitz.Rect(rect) * M
            H, W = self.cv.winfo_height(), self.cv.winfo_width()
            self.cv.configure(scrollregion=(0, 0, lay["cw"], max(lay["total"], H)))
            y_ = lay["ys"][i] + (r_.y0 + r_.y1) / 2 - H / 2
            x_ = lay["xs"][i] + (r_.x0 + r_.x1) / 2 - W / 2
            self._scroll_a(y_, x_ if lay["cw"] > W else None)
            self.dibujar()
            sincronizar(self)

        def _ir_txt(self, *_):
            try:
                self.ir(int(self.v_pag.get().strip()) - 1)
            except ValueError:
                pass
            self.cv.focus_set()

        # ---- zoom
        def pct_actual(self):
            lay = self.lay
            if not lay:
                return 100.0
            return lay["zs"][min(self.pag, len(lay["zs"]) - 1)] / PX_PT * 100

        def poner_zoom(self, valor, ancla=None):
            if isinstance(valor, str) and valor.endswith("%"):
                valor = float(valor.replace("%", "").strip())
            lay = self.layout()
            punto = None
            if lay:
                ax, ay = ancla if ancla else (self.cv.winfo_width() / 2, self.cv.winfo_height() / 2)
                cx_, cy_ = self.cv.canvasx(ax), self.cv.canvasy(ay)
                i = self.pagina_en(cy_, cx_)
                punto = (i, (cx_ - lay["xs"][i]) / max(1, lay["ws"][i]), (cy_ - lay["ys"][i]) / max(1, lay["hs"][i]),
                         ax, ay)
            if isinstance(valor, (int, float)):
                valor = max(5.0, min(1600.0, float(valor)))
                self.zoom = valor
                self.v_zoom.set(f"{valor:g} %")
            else:
                self.zoom = valor
                self.v_zoom.set(valor)
            self.reanclar = False  # el punto lo fija el zoom
            lay = self.layout()
            if lay and punto:
                i, fx, fy, ax, ay = punto
                self.cv.configure(scrollregion=(0, 0, lay["cw"], max(lay["total"], self.cv.winfo_height())))
                self._scroll_a(lay["ys"][i] + fy * lay["hs"][i] - ay, lay["xs"][i] + fx * lay["ws"][i] - ax)
            self.reanclar = None
            self.dibujar()
            sincronizar(self)

        def zoom_paso(self, d, ancla=None):
            if self.t and self.t.get("modo_vista") == "mosaico" and self.zoom == "Miniaturas" and self.lay:
                # v3.6: miniaturas: se agrandan o achican todas por igual
                tm_ = getattr(self, "tam_mini", px(170))
                maximo = max(px(80), self.cv.winfo_width() - 60)
                nuevo_ = max(px(70), min(maximo, tm_ * 1.25 if d > 0 else tm_ / 1.25))
                if abs(nuevo_ - tm_) < 1:
                    return
                ax, ay = ancla if ancla else (self.cv.winfo_width() / 2, self.cv.winfo_height() / 2)
                i = self.pagina_en(self.cv.canvasy(ay), self.cv.canvasx(ax))
                self.tam_mini = nuevo_
                self.reanclar = False
                self.lay_k = None
                lay = self.layout()
                self.reanclar = None
                if lay:
                    self.cv.configure(scrollregion=(0, 0, lay["cw"], max(lay["total"], self.cv.winfo_height())))
                    self._scroll_a(max(0, lay["ys"][i] + lay["hs"][i] / 2 - ay))
                self.dibujar()
                sincronizar(self)
                return
            pct = self.pct_actual()
            if d > 0:
                nuevo = next((p_ for p_ in PASOS_ZOOM if p_ > pct + 0.5), PASOS_ZOOM[-1])
            else:
                nuevo = next((p_ for p_ in reversed(PASOS_ZOOM) if p_ < pct - 0.5), PASOS_ZOOM[0])
            self.poner_zoom(nuevo, ancla)

        # ---- activo / pestana
        def es_activa(self):
            return self.t is not None and self.t is pest_activa()

        def activar(self):
            if self.t is not None and not self.es_activa() and self.t in pest:
                activar_pestana(pest.index(self.t), mostrar_visor=False)
            self.cv.focus_set()

        def poner(self, t_):
            if t_ is not self.t:
                self.t = t_
                self.lay = self.lay_k = None
                self.reanclar = None
                self.pag = t_.get("pag", 0) if t_ else 0
                if t_ is not None:
                    self.zoom = t_.get("zoom", "Ajustar ancho")
                    self.v_zoom.set(f"{self.zoom:g} %" if isinstance(self.zoom, float) else self.zoom)
                    self._pendiente_pos = (self.pag, t_.get("frac", 0.0))
            self.v_nom.set(t_["nombre"] if (t_ and vis["comp"]) else "")
            if t_ and vis["comp"]:
                self.l_nom.grid(row=1, column=0, columnspan=2, sticky="ew", padx=14, pady=(0, 2))
            else:
                self.l_nom.grid_remove()

        def recordar(self):
            if self.t is not None and self.lay:
                p_, f_ = self.posicion()
                self.t.update(pag=p_, frac=f_, zoom=self.zoom)

        # ---- dibujo (solo lo visible)
        def dibujar(self, *_):
            self.job = None
            if app["pagina"] != "visor" or not self.marco.winfo_ismapped():
                return
            cv_ = self.cv
            cv_.configure(bg=col("campo"))
            cv_.delete("all")
            self.marco.configure(border_color=C["acento"] if (vis["comp"] and self.es_activa()) else C["borde"])
            t_ = self.t
            W, H = max(cv_.winfo_width(), 200), max(cv_.winfo_height(), 150)
            if not t_:
                cv_.configure(scrollregion=(0, 0, W, H))
                self.v_tot.set("")
                self.v_pag.set("")
                cv_.create_image(W // 2, H // 2 - 60, image=logo_grande)
                cv_.create_text(W // 2, H // 2 + 20, text="Abrí un PDF para empezar", fill=col("texto"),
                                font=(FAM, 15, "bold"))
                cv_.create_text(W // 2, H // 2 + 48, text="«Abrir» arriba, Ctrl+O, o arrastrá el PDF sobre PdFOL.exe.",
                                fill=col("texto2"), font=(FAM, 11))
                self.ult = []
                enviar_pedidos()
                return
            lay = self.layout()
            if not lay:
                cv_.configure(scrollregion=(0, 0, W, H))
                cv_.create_text(W // 2, H // 2, text="Abriendo " + t_["nombre"] + "…", fill=col("texto2"),
                                font=(FAM, 12))
                return
            n = len(lay["pags"])
            self.v_tot.set(f"de {n}")
            cv_.configure(scrollregion=(0, 0, lay["cw"], max(lay["total"], H)))
            pend = getattr(self, "_pendiente_pos", None)
            if pend is not None:
                self._pendiente_pos = None
                self.ir_pos(*pend)
            elif self.reanclar:
                p_, f_ = self.reanclar
                self.ir_pos(p_, f_)
            self.reanclar = None
            y0, y1 = cv_.canvasy(0), cv_.canvasy(0) + H
            x0v, x1v = cv_.canvasx(0), cv_.canvasx(0) + W
            i0, i1 = self.pagina_en(y0), self.pagina_en(y1)
            while i1 + 1 < len(lay["ys"]) and lay["ys"][i1 + 1] == lay["ys"][i1]:
                i1 += 1  # v3.0: la segunda pagina de la ultima fila tambien se dibuja
            actual = self.pagina_en(y0 + H * 0.4)
            if actual != self.pag or self.v_pag.get() != str(actual + 1):
                self.pag = actual
                if raiz.focus_get() is not self.e_pag._entry:
                    self.v_pag.set(str(actual + 1))
                if self.es_activa():
                    t_["pag"] = actual
                    mini_ver(actual, solo_si_fuera=True)
                    mini_pedir_dibujo()
            folio_f, firma = folio_de_posicion(n)
            parar = lay["parar"]
            busq = vis["busq"] if (vis["busq"] and vis["busq"]["tab"] == t_["id"]) else None
            pedidos = []
            for i in range(i0, i1 + 1):
                ruta, pag, rot = lay["pags"][i]
                x, y, w_, h_, z = lay["xs"][i], lay["ys"][i], lay["ws"][i], lay["hs"][i], lay["zs"][i]
                fol_ = folio_f(i)
                base = ("t", ruta, pag, rot, round(z, 5), parar, firma if fol_ else None,
                        fol_[1] if fol_ else None, ver_arch(ruta))
                cv_.create_rectangle(x + 3, y + 3, x + w_ + 3, y + h_ + 3, fill=col("borde"), outline="")
                cv_.create_rectangle(x, y, x + w_, y + h_, fill="#FFFFFF", outline="")
                if w_ * h_ <= MAX_PIXELES_VISOR:
                    trozos = [None]
                else:  # solo los mosaicos que se ven
                    T_ = MOSAICO_VISOR
                    ta, tb = max(0, int((x0v - x) // T_)), int((min(x1v, x + w_) - x) // T_)
                    ua, ub = max(0, int((y0 - y) // T_)), int((min(y1, y + h_) - y) // T_)
                    trozos = [(tx * T_, ty * T_, min(w_, (tx + 1) * T_), min(h_, (ty + 1) * T_))
                              for ty in range(ua, ub + 1) for tx in range(ta, tb + 1)
                              if tx * T_ < w_ and ty * T_ < h_]
                falta = False
                for tr in trozos:
                    k_ = base + (tr,)
                    ft = vis["cache"].get(k_)
                    if ft is not None:
                        cv_.create_image(x + (tr[0] if tr else 0), y + (tr[1] if tr else 0), image=ft, anchor="nw")
                        if k_ in vis["lru"]:
                            vis["lru"].remove(k_)
                        vis["lru"].append(k_)
                    else:
                        falta = True
                        pedidos.append((k_, ruta, pag, z, rot, parar, fol_, tr))
                if falta and trozos == [None]:
                    cv_.create_text(x + w_ // 2, y + min(h_ // 2, 120), text=f"Página {i + 1}…",
                                    fill="#9AA6B4", font=(FAM, 11))
                if vis["comp"]:  # v3.5: comparando: numero de la hoja (se toma de ahi) y marco si esta elegida
                    sel_p = i in (org_de(t_).get("sel") or ())
                    if sel_p:
                        cv_.create_rectangle(x - 4, y - 4, x + w_ + 4, y + h_ + 4, outline=col("acento"), width=4)
                    etq_ = f"⠿  Pág. {i + 1}" if w_ > px(150) else f"⠿ {i + 1}"
                    bw_ = px(22) + px(7) * len(etq_)
                    x0_ = x + w_ - 6 - bw_  # arriba a la derecha: casi nunca tapa el texto
                    cv_.create_rectangle(x0_, y + 6, x0_ + bw_, y + 6 + px(24), outline="",
                                         fill=col("acento") if sel_p else "#3B4656", tags=("ins", f"ins{i}"))
                    cv_.create_text(x0_ + bw_ / 2, y + 6 + px(12), text=etq_, fill="#FFFFFF",
                                    font=(FAM, 9, "bold"), tags=("ins", f"ins{i}"))
                for s_ in vis.get("img_sel") or ():  # v3.4: imagenes elegidas para copiar
                    if s_["ruta"] == ruta and s_["pag"] == pag:
                        M_ = matriz_vista(lay["dims"][i][0], lay["dims"][i][1], z, rot, parar)
                        q_ = fitz.Rect(s_["bbox"]) * M_
                        cv_.create_rectangle(x + q_.x0, y + q_.y0, x + q_.x1, y + q_.y1, outline="", fill="#0EA5E9",
                                             stipple="gray25")
                        cv_.create_rectangle(x + q_.x0, y + q_.y0, x + q_.x1, y + q_.y1, outline="#0EA5E9", width=3)
                # resaltados (guardables) y resultados de la busqueda
                items_ = [it_ for it_ in vis["res"].get(ruta, {}).get(pag, []) if it_["tipo"] != "giro"]
                if items_:
                    M = matriz_vista(lay["dims"][i][0], lay["dims"][i][1], z, rot, parar)
                    ined_ = vis.get("ined")
                    for it_ in items_:
                        if ined_ and ined_["it"] is it_:
                            continue  # v4.1: se esta escribiendo encima
                        bx_, by_, ft_ = capa_item(it_, M, (round(z, 5), rot, parar))
                        cv_.create_image(x + bx_, y + by_, anchor="nw", image=ft_)
                    e_ = vis.get("edit_item")  # v2.6: la firma o el texto elegido, con su marco y tirador
                    if (e_ and e_[0] == ruta and e_[1] == pag and app.get("panel") in ("firmar", "texto") and not ined_
                            and e_[2]["tipo"] in ("texto_n", "reemplazo")):  # v4.1: recuadro como Word
                        q0_ = fitz.Rect(caja_texto(e_[2])) * M
                        dibujar_marco_word(cv_, x + q0_.x0 - 3, y + q0_.y0 - 3, x + q0_.x1 + 3, y + q0_.y1 + 3, "marco")
                    elif e_ and e_[0] == ruta and e_[1] == pag and app.get("panel") in ("firmar", "texto") and not ined_:
                        rr_ = fitz.Rect(e_[2]["rect"])
                        qs_ = [q_ * M for q_ in (rr_.tl, rr_.tr, rr_.br, rr_.bl)]
                        cv_.create_rectangle(x + min(q.x for q in qs_) - 2, y + min(q.y for q in qs_) - 2,
                                             x + max(q.x for q in qs_) + 2, y + max(q.y for q in qs_) + 2,
                                             outline=col("acento"), width=2, dash=(5, 3))
                        if e_[2]["tipo"] == "firma":
                            q_ = rr_.br * M
                            cv_.create_oval(x + q_.x - 7, y + q_.y - 7, x + q_.x + 7, y + q_.y + 7,
                                            fill=col("acento"), outline="#FFFFFF", width=2)
                sel_ = vis.get("seleccion")
                if sel_ and sel_["vista"] is self and sel_["base"][0] == i:
                    chars_ = caracteres_de(ruta, pag) or []
                    a_s, b_s = sorted((sel_["a"], sel_["b"]))
                    rs_ = rects_seleccion(chars_, a_s, b_s)
                    if rs_:
                        M = matriz_vista(lay["dims"][i][0], lay["dims"][i][1], z, rot, parar)
                        bx_, by_, im_ = imagen_item({"tipo": "texto", "rects": rs_, "color": (70, 140, 255),
                                                     "op": 0.32}, M)
                        self._ft_sel = ImageTk.PhotoImage(im_)
                        cv_.create_image(x + bx_, y + by_, anchor="nw", image=self._ft_sel)
                capas_ = []
                if busq and i in busq["por_pos"]:
                    act_ = busq["hits"][busq["i"]] if 0 <= busq["i"] < len(busq["hits"]) else None
                    for r_ in busq["por_pos"][i]:
                        capas_.append((r_, NARANJA if act_ and act_[0] == i and act_[1] == r_ else AMARILLO))
                if capas_:
                    M = matriz_vista(lay["dims"][i][0], lay["dims"][i][1], z, rot, parar)
                    for r_, color_ in capas_:
                        rr = fitz.Rect(r_) * M
                        cv_.create_image(x + rr.x0, y + rr.y0, anchor="nw",
                                         image=capa_color(rr.width + 1, rr.height + 1, color_))
            # adelantar la pagina siguiente y la anterior (si son de una sola pieza)
            for i in (i1 + 1, i0 - 1):
                if 0 <= i < n and lay["ws"][i] * lay["hs"][i] <= MAX_PIXELES_VISOR:
                    ruta, pag, rot = lay["pags"][i]
                    fol_ = folio_f(i)
                    k_ = ("t", ruta, pag, rot, round(lay["zs"][i], 5), parar, firma if fol_ else None,
                          fol_[1] if fol_ else None, ver_arch(ruta), None)
                    if k_ not in vis["cache"]:
                        pedidos.append((k_, ruta, pag, lay["zs"][i], rot, parar, fol_, None))
            self.ult = pedidos
            enviar_pedidos()
            if vis["modo_res"]:
                self._previa()
            if vis.get("ined"):  # v4.1: el cuadro de escritura sobre la hoja
                ined_colocar(self)

        # ---- raton: arrastrar desplaza; con el resaltador marca (Texto / Área o polilínea / Libre)
        def _punto_pagina(self, cx_, cy_, i=None):
            lay = self.lay
            if not lay:
                return None
            if i is None:
                i = self.pagina_en(cy_, cx_)
                x, y = lay["xs"][i], lay["ys"][i]
                if not (x <= cx_ <= x + lay["ws"][i] and y <= cy_ <= y + lay["hs"][i]):
                    return None
            x, y = lay["xs"][i], lay["ys"][i]
            ruta, pag, rot = lay["pags"][i]
            M = matriz_vista(lay["dims"][i][0], lay["dims"][i][1], lay["zs"][i], rot, lay["parar"])
            return i, ruta, pag, M, x, y

        def _pt(self, ev, base):
            """Punto del evento en coordenadas de la pagina 'base' (i, ruta, pag, M, x, y)."""
            _i, _r, _p, M, x, y = base
            return tuple(fitz.Point(self.cv.canvasx(ev.x) - x, self.cv.canvasy(ev.y) - y) * ~M)

        def _press(self, ev):
            self.activar()
            self._ed = None
            self._parr = None
            if vis["comp"] and self.t is not None:  # v3.5: comparando, el numero de la hoja la elige
                i_ins = insignia_en(self, ev)
                base_ = self._punto_pagina(self.cv.canvasx(ev.x), self.cv.canvasy(ev.y))
                if i_ins is None and base_ and self.t.get("modo_vista") == "mosaico":
                    i_ins = base_[0]  # v3.6: en miniaturas se toma la hoja de cualquier parte
                if i_ins is not None:
                    pagina_press(self, i_ins, ev)
                    return
                if base_:
                    vis["pag_clic"] = (self.t["id"], base_[0])
                    if org.get("sel") and not (ev.state & 0x5):
                        org["sel"] = set()
                        visor_pedir_dibujo()
            if (app["pagina"] == "visor" and app.get("panel") not in ("firmar", "texto") and not vis["modo_res"]
                    and self.t is not None):  # v4.1.1: clic en un texto puesto: se elige (se abre el panel Texto)
                b_t = self._punto_pagina(self.cv.canvasx(ev.x), self.cv.canvasy(ev.y))
                if b_t:
                    pt_t = fitz.Point(self._pt(ev, b_t))
                    if any(it_["tipo"] in ("texto_n", "reemplazo") and fitz.Rect(caja_texto(it_)).contains(pt_t)
                           for it_ in vis["res"].get(b_t[1], {}).get(b_t[2], [])):
                        abrir_panel("texto")
            if app["pagina"] == "visor" and app.get("panel") in ("firmar", "texto") and not vis["modo_res"]:
                if edicion_press(self, ev):  # v2.6: firmar, sellar y texto
                    if not getattr(self, "_ed", None):
                        # v2.7: el arrastre que sigue al clic (o a la ventanita) no mueve la hoja: antes volvia a la pag. 1
                        self._ed = {"modo": "nada"}
                    return
            if not vis["modo_res"]:
                self._arrastre_mano = False
                if v_herr.get() == "Seleccionar":
                    cx_, cy_ = self.cv.canvasx(ev.x), self.cv.canvasy(ev.y)
                    base = self._punto_pagina(cx_, cy_)
                    chars = caracteres_de(base[1], base[2]) if base else None
                    if base and chars == [] and ocr_pedir(base[1], base[2]):  # v4.1: escaneo: se reconoce
                        chars = None
                    if base:  # v3.4: clic sobre una imagen (no sobre texto): se elige para copiarla
                        pi_ = fitz.Point(self._pt(ev, base))
                        sobre_txt = bool(chars) and any(c_[0] - 1 <= pi_.x <= c_[2] + 1 and c_[1] - 1 <= pi_.y <= c_[3] + 1
                                                        for c_ in chars)
                        im_ = None if (sobre_txt or es_escaneo(base[1], base[2])) else imagen_en(base[1], base[2], pi_,
                                                                                                  sin_fondo=True)
                        if im_:
                            vis["seleccion"] = None
                            elegir_imagen(im_, bool(ev.state & 0x4))
                            self._arrastre_mano = True  # arrastrar igual desplaza la hoja
                            self.cv.scan_mark(ev.x, ev.y)
                            return
                        if vis.get("img_sel") and not (ev.state & 0x4):
                            vis["img_sel"] = []
                            visor_pedir_dibujo()
                    if base and chars:  # sobre texto: empieza a seleccionar
                        k_ = char_cercano(chars, self._pt(ev, base))
                        vis["seleccion"] = {"vista": self, "base": base, "a": k_, "b": k_}
                        visor_pedir_dibujo()
                        return
                    if vis.get("seleccion"):  # clic fuera del texto: se quita la seleccion
                        vis["seleccion"] = None
                        visor_pedir_dibujo()
                self._arrastre_mano = True  # Mano (o zona sin texto): arrastrar desplaza
                self.cv.scan_mark(ev.x, ev.y)
                self.cv.configure(cursor="fleur")
                return
            cx_, cy_ = self.cv.canvasx(ev.x), self.cv.canvasy(ev.y)
            modo = v_res_modo.get()
            pol = getattr(self, "_poly", None)
            if modo == "Área" and pol:  # polilinea en curso: cada clic suma un vertice
                p_ = self._pt(ev, pol["base"])
                q0 = fitz.Point(pol["pts"][0]) * pol["base"][3]
                if len(pol["pts"]) >= 3 and abs(q0.x + pol["base"][4] - cx_) + abs(q0.y + pol["base"][5] - cy_) < 12:
                    self.cerrar_poligono()
                else:
                    pol["pts"].append(p_)
                    self._previa()
                return
            base = self._punto_pagina(cx_, cy_)
            if not base:
                return
            p_ = self._pt(ev, base)
            if modo == "Texto":
                chars = caracteres_de(base[1], base[2])
                if chars is None:
                    v_estado.set("Leyendo el texto de la página… probá de nuevo en un instante.")
                    self._sel = None
                    return
                if not chars:
                    v_estado.set("Esta página no tiene texto (plano escaneado): usá «Área» o «Libre».")
                    self._sel = None
                    return
                k_ = char_cercano(chars, p_)
                self._sel = {"base": base, "a": k_, "b": k_}
                self._previa()
            elif modo == "Área":
                self._area = {"base": base, "p0": p_, "p1": p_, "x": ev.x, "y": ev.y, "arrastre": False}
            else:
                self._trazo = {"base": base, "pts": [p_]}

        def _motion(self, ev):
            if getattr(self, "_parr", None):
                pagina_motion(self, ev)
                return
            if getattr(self, "_ed", None):
                edicion_motion(self, ev)
                return
            if not vis["modo_res"]:
                sel_ = vis.get("seleccion")
                if sel_ and sel_["vista"] is self and not getattr(self, "_arrastre_mano", False):
                    chars = caracteres_de(sel_["base"][1], sel_["base"][2]) or []
                    if chars:
                        sel_["b"] = char_cercano(chars, self._pt(ev, sel_["base"]))
                        self.dibujar()
                    if ev.y < 20:  # seguir seleccionando hacia arriba o abajo
                        self.cv.yview_scroll(-1, "units")
                    elif ev.y > self.cv.winfo_height() - 20:
                        self.cv.yview_scroll(1, "units")
                    return
                self.cv.scan_dragto(ev.x, ev.y, gain=1)
                self.movido()
                return
            sel, area, trazo = getattr(self, "_sel", None), getattr(self, "_area", None), getattr(self, "_trazo", None)
            if sel:
                chars = caracteres_de(sel["base"][1], sel["base"][2]) or []
                if chars:
                    sel["b"] = char_cercano(chars, self._pt(ev, sel["base"]))
                    self._previa()
            elif area:
                area["p1"] = self._pt(ev, area["base"])
                if abs(ev.x - area["x"]) + abs(ev.y - area["y"]) > 5:
                    area["arrastre"] = True
                self._previa()
            elif trazo:
                p_ = self._pt(ev, trazo["base"])
                q_ = trazo["pts"][-1]
                z = abs(trazo["base"][3].a) + abs(trazo["base"][3].b)
                if (p_[0] - q_[0]) ** 2 + (p_[1] - q_[1]) ** 2 > (1.5 / max(z, 0.01)) ** 2:
                    trazo["pts"].append(p_)
                    self._previa()

        def _mover_libre(self, ev):
            """Sin boton: la polilinea sigue al mouse; en modo Texto se lee el texto de la pagina de antemano."""
            if app.get("panel") == "texto" and (vis.get("ined") or vis.get("edit_item")):  # v4.1.1: tiradores
                cx_, cy_ = self.cv.canvasx(ev.x), self.cv.canvasy(ev.y)
                ed = vis.get("ined")
                t_ = None
                if ed and ed["vista"] is self and ed.get("caja"):
                    t_ = tirador_en(ed["caja"], cx_, cy_)
                    if t_ == "dentro":
                        t_ = None
                elif not ed:
                    e_ = vis["edit_item"]
                    b_ = self._punto_pagina(cx_, cy_)
                    if b_ and e_[2]["tipo"] in ("texto_n", "reemplazo") and e_[0] == b_[1] and e_[1] == b_[2]:
                        t_ = tirador_en(caja_item_vista(self, e_[2], b_), cx_, cy_)
                if t_ != getattr(self, "_t_cursor", None):
                    self._t_cursor = t_
                    cursor_tirador(self.cv, t_)
                if t_:
                    return
            if vis["comp"]:  # v3.5: la manito sobre el numero de la hoja (se puede tomar y arrastrar)
                sobre_ = insignia_en(self, ev) is not None
                if sobre_ != getattr(self, "_sobre_ins", False):
                    self._sobre_ins = sobre_
                    self.cv.configure(cursor="hand2" if sobre_ else cursor_herramienta())
                if sobre_:
                    return
            if not vis["modo_res"]:
                if v_herr.get() == "Seleccionar":
                    base = self._punto_pagina(self.cv.canvasx(ev.x), self.cv.canvasy(ev.y))
                    if base:
                        caracteres_de(base[1], base[2])
                return
            pol = getattr(self, "_poly", None)
            if pol:
                self._previa(extra=self._pt(ev, pol["base"]))
            elif v_res_modo.get() == "Texto":
                base = self._punto_pagina(self.cv.canvasx(ev.x), self.cv.canvasy(ev.y))
                if base:
                    caracteres_de(base[1], base[2])

        def _release(self, ev):
            if getattr(self, "_parr", None):
                pagina_release(self, ev)
                return
            if getattr(self, "_ed", None):
                edicion_release(self, ev)
                return
            if not vis["modo_res"]:
                self.cv.configure(cursor=cursor_herramienta())
                sel_ = vis.get("seleccion")
                if sel_ and sel_["a"] == sel_["b"] and not getattr(self, "_doble", False):
                    vis["seleccion"] = None  # un clic sin arrastrar no selecciona
                    visor_pedir_dibujo()
                elif sel_:
                    n_ = len(texto_seleccion())
                    v_estado.set(f"{n_} caracteres seleccionados · Ctrl+C copia · clic derecho: más opciones.")
                self._doble = False
                return
            sel, area, trazo = getattr(self, "_sel", None), getattr(self, "_area", None), getattr(self, "_trazo", None)
            self._sel = self._area = self._trazo = None
            if sel:
                chars = caracteres_de(sel["base"][1], sel["base"][2]) or []
                a_, b_ = sorted((sel["a"], sel["b"]))
                rects = rects_seleccion(chars, a_, b_)
                if rects:
                    vis["texto_sel"] = "".join(c_[5] for c_ in chars[a_:b_ + 1])
                    nuevo_resaltado(sel["base"][1], sel["base"][2], "texto", rects=rects)
            elif area:
                if area["arrastre"]:
                    r_ = fitz.Rect(area["p0"], area["p1"]).normalize()
                    nuevo_resaltado(area["base"][1], area["base"][2], "rect", rects=[tuple(r_)])
                else:  # un clic: empieza una polilinea (clics suman vertices; doble clic o Enter cierra)
                    self._poly = {"base": area["base"], "pts": [area["p0"]]}
                    v_estado.set("Polilínea: hacé clic en cada vértice. Doble clic, Enter o clic en el primer punto "
                                 "la cierra. Esc la cancela.")
            elif trazo and len(trazo["pts"]) > 1:
                z = abs(trazo["base"][3].a) + abs(trazo["base"][3].b)
                nuevo_resaltado(trazo["base"][1], trazo["base"][2], "libre", pts=trazo["pts"],
                                ancho=14 / max(z, 0.01))
            self.cv.delete("previa")
            self._previa()

        def _doble_clic(self, ev, renglon=False):
            """Doble clic: la palabra; triple clic: el renglon (o cierra la polilinea)."""
            if vis["comp"] and self.t and self.t.get("modo_vista") == "mosaico" and not renglon:
                agrandar_hoja(self, ev)  # v3.6: miniatura <-> hoja grande
                return
            if app.get("panel") == "texto" and not renglon and edicion_doble(self, ev):
                return
            if getattr(self, "_poly", None):
                self.cerrar_poligono()
                return
            if vis["modo_res"] or v_herr.get() != "Seleccionar":
                return
            base = self._punto_pagina(self.cv.canvasx(ev.x), self.cv.canvasy(ev.y))
            chars = caracteres_de(base[1], base[2]) if base else None
            if not chars:
                return
            k_ = char_cercano(chars, self._pt(ev, base))
            lid = chars[k_][4]
            a_ = b_ = k_
            if renglon:
                while a_ > 0 and chars[a_ - 1][4] == lid:
                    a_ -= 1
                while b_ < len(chars) - 1 and chars[b_ + 1][4] == lid:
                    b_ += 1
            else:
                while a_ > 0 and chars[a_ - 1][4] == lid and not chars[a_ - 1][5].isspace():
                    a_ -= 1
                while b_ < len(chars) - 1 and chars[b_ + 1][4] == lid and not chars[b_ + 1][5].isspace():
                    b_ += 1
            vis["seleccion"] = {"vista": self, "base": base, "a": a_, "b": b_}
            self._doble = True
            visor_pedir_dibujo()

        def cerrar_poligono(self, *_):
            pol = getattr(self, "_poly", None)
            self._poly = None
            if pol and len(pol["pts"]) >= 3:
                nuevo_resaltado(pol["base"][1], pol["base"][2], "poli", pts=pol["pts"])
            self.cv.delete("previa")

        def _previa(self, extra=None):
            """Dibuja lo que se esta marcando (antes de soltar)."""
            self.cv.delete("previa")
            item, base = None, None
            sel, area = getattr(self, "_sel", None), getattr(self, "_area", None)
            trazo, pol = getattr(self, "_trazo", None), getattr(self, "_poly", None)
            if sel:
                chars = caracteres_de(sel["base"][1], sel["base"][2]) or []
                a_, b_ = sorted((sel["a"], sel["b"]))
                item, base = {"tipo": "texto", "rects": rects_seleccion(chars, a_, b_)}, sel["base"]
            elif area and area["arrastre"]:
                item, base = {"tipo": "rect", "rects": [tuple(fitz.Rect(area["p0"], area["p1"]).normalize())]}, area["base"]
            elif trazo:
                z = abs(trazo["base"][3].a) + abs(trazo["base"][3].b)
                item, base = {"tipo": "libre", "pts": trazo["pts"], "ancho": 14 / max(z, 0.01)}, trazo["base"]
            elif pol:
                pts = pol["pts"] + ([extra] if extra else [])
                item, base = {"tipo": "poli" if len(pts) > 2 else "libre", "pts": pts, "ancho": 2 / max(
                    abs(pol["base"][3].a) + abs(pol["base"][3].b), 0.01)}, pol["base"]
                for p_ in pol["pts"]:
                    q_ = fitz.Point(p_) * pol["base"][3]
                    self.cv.create_oval(q_.x + base[4] - 4, q_.y + base[5] - 4, q_.x + base[4] + 4, q_.y + base[5] + 4,
                                        fill=col("acento"), outline="#FFFFFF", tags="previa")
            if not item or (item.get("rects") == []):
                return
            item.update(color=vis["res_color"], op=float(v_res_op.get()), id=-1)
            bx, by, img = imagen_item(item, base[3])
            ft = ImageTk.PhotoImage(img)
            self._ft_previa = ft
            self.cv.create_image(base[4] + bx, base[5] + by, image=ft, anchor="nw", tags="previa")
            self.cv.tag_raise("previa")

        def _menu(self, ev):
            self.activar()
            cx_, cy_ = self.cv.canvasx(ev.x), self.cv.canvasy(ev.y)
            pp = self._punto_pagina(cx_, cy_)
            m_ = menu_contextual()
            if pp:
                i, ruta, pag, M, x, y = pp
                p_ = fitz.Point(cx_ - x, cy_ - y) * ~M
                m_.add_titulo(f"Página {i + 1}" + (f" de {len(self.lay['pags'])}" if self.lay else ""))  # v4.2
                if vis["comp"] and org.get("orden"):  # v3.5: comparando, la hoja se copia, corta o pega
                    if i not in org["sel"]:
                        org["sel"], org["ancla"] = {i}, i
                        visor_pedir_dibujo()
                    vis["pag_clic"] = (self.t["id"], i)
                    n_s = len(org["sel"])
                    que_p = f"la página {i + 1}" if n_s == 1 else f"{n_s} páginas"
                    m_.add_command(label=f"Copiar {que_p}", command=lambda: teclas_paginas("c"), acelerador="Ctrl+C",
                                   punto="#0EA5E9")
                    m_.add_command(label=f"Cortar {que_p}", command=lambda: teclas_paginas("x"), acelerador="Ctrl+X")
                    n_c = len(org.get("copiado") or [])
                    if n_c:
                        m_.add_command(label=f"Pegar {n_c} página(s) después de la {max(org['sel']) + 1}",
                                       command=lambda: teclas_paginas("v"), acelerador="Ctrl+V")
                        m_.add_command(label=f"Pegar {n_c} página(s) antes de la {min(org['sel']) + 1}",
                                       command=lambda: (org_insertar(list(org["copiado"]), min(org["sel"])),
                                                        [setattr(w_, "lay_k", None) for w_ in vistas],
                                                        visor_pedir_dibujo()))
                    m_.add_command(label=f"Quitar {que_p}", acelerador="Supr", punto="#EF4444",
                                   command=lambda: (org_eliminar(), [setattr(w_, "lay_k", None) for w_ in vistas],
                                                    visor_pedir_dibujo()))
                    m_.add_separator()
                toco = [it for it in vis["res"].get(ruta, {}).get(pag, []) if item_contiene(it, p_)]
                if toco:
                    que_ = {"firma": "Quitar esta firma o sello", "texto_n": "Quitar este texto",
                            "reemplazo": "Deshacer este cambio de texto"}.get(toco[-1]["tipo"], "Quitar este resaltado")
                    m_.add_command(label=que_, command=lambda: quitar_resaltado(ruta, pag, toco[-1]),
                                   punto="#EF4444")
                    m_.add_separator()
                im_ = imagen_en(ruta, pag, p_, sin_fondo=True) if not toco and not es_escaneo(ruta, pag) else None
                if im_ and not any(misma_img(im_, x_) for x_ in vis.get("img_sel") or []):
                    elegir_imagen(im_)
                n_im = len(vis.get("img_sel") or [])
                todas_ = imagenes_de(ruta, pag)
                if n_im:
                    m_.add_command(label="Copiar imagen (pegala en una carpeta, Word, WhatsApp…)" if n_im == 1
                                   else f"Copiar {n_im} imágenes", command=copiar_imagenes, acelerador="Ctrl+C",
                                   punto="#0EA5E9")
                    m_.add_command(label="Guardar imagen como…" if n_im == 1 else f"Guardar {n_im} imágenes en…",
                                   command=guardar_imagenes_como)
                if len(todas_) > 1 or (todas_ and not n_im):
                    m_.add_command(label=f"Copiar todas las imágenes de esta página ({len(todas_)})",
                                   command=lambda: copiar_imagenes(list(todas_)))
                if n_im or todas_:
                    m_.add_separator()
                oc_ = ocr_de(ruta, pag)  # v4.1: escaneos
                if oc_ and oc_.get("letras"):
                    m_.add_command(label="Copiar todo el texto reconocido de esta página", punto="#8B5CF6",
                                   command=lambda: copiar_texto_ocr(ruta, pag))
                    m_.add_separator()
                elif not oc_ and (es_escaneo(ruta, pag) or caracteres_de(ruta, pag) == []):
                    m_.add_command(label="Reconocer el texto de esta página (OCR)", punto="#8B5CF6",
                                   command=lambda: ocr_pedir(ruta, pag, forzar=True))
                    m_.add_separator()
            punto = "#%02x%02x%02x" % tuple(vis["res_color"])
            if vis.get("seleccion"):
                txt_ = texto_seleccion().strip().replace("\n", " ")
                m_.add_command(label="Copiar", command=copiar_seleccion, acelerador="Ctrl+C")
                m_.add_command(label="Resaltar la selección", command=resaltar_seleccion, punto=punto)
                if txt_:
                    m_.add_command(label=f"Buscar «{txt_[:24] + ('…' if len(txt_) > 24 else '')}»",
                                   command=lambda: (e_buscar.delete(0, "end"), e_buscar.insert(0, txt_),
                                                    buscar_texto(txt_)))
                m_.add_separator()
            m_.add_command(label="Seleccionar toda la página", command=lambda: seleccionar_pagina(self),
                           acelerador="Ctrl+A")
            m_.add_separator()
            m_.add_command(label="Resaltar texto", command=lambda: activar_resaltador("Texto"), punto=punto)
            m_.add_command(label="Resaltar área / polilínea", command=lambda: activar_resaltador("Área"), punto=punto)
            m_.add_command(label="Resaltar a mano alzada", command=lambda: activar_resaltador("Libre"), punto=punto)
            if vis.get("texto_sel"):
                m_.add_command(label="Copiar texto resaltado", command=copiar_texto_sel, acelerador="")
            m_.add_separator()
            m_.add_command(label="Buscar…", command=enfocar_busqueda, acelerador="Ctrl+F")
            m_.add_separator()
            m_.add_command(label="Acercar", command=lambda: self.zoom_paso(1, (ev.x, ev.y)), acelerador="Ctrl + rueda")
            m_.add_command(label="Alejar", command=lambda: self.zoom_paso(-1, (ev.x, ev.y)))
            m_.add_command(label="Ajustar ancho", command=lambda: self.poner_zoom("Ajustar ancho"), acelerador="Ctrl+0")
            m_.add_command(label="Página entera", command=lambda: self.poner_zoom("Página entera"))
            m_.tk_popup(ev.x_root, ev.y_root)

        def _teclas(self, ev):
            k_ = ev.keysym
            ctrl = bool(ev.state & 0x4)
            if ctrl and k_ in ("plus", "equal", "KP_Add"):
                self.zoom_paso(1)
            elif ctrl and k_ in ("minus", "KP_Subtract"):
                self.zoom_paso(-1)
            elif ctrl and k_ in ("0", "KP_0"):
                self.poner_zoom("Ajustar ancho")
            elif ctrl and (k_.lower() == "y" or (k_ == "Z" and ev.state & 0x1)):
                rehacer_edicion()
            elif ctrl and k_.lower() == "z":
                if hist["atras"]:
                    deshacer_edicion()
                elif vis["res_pila"]:
                    deshacer_resaltado()
                else:
                    org_deshacer()
            elif (k_ in ("Left", "Right", "Up", "Down") and not ctrl and vis.get("edit_item")
                  and app.get("panel") in ("texto", "firmar")):
                d_ = 10 if ev.state & 0x1 else 1  # Shift: mas rapido
                mover_editado(*{"Left": (-d_, 0), "Right": (d_, 0), "Up": (0, -d_), "Down": (0, d_)}[k_])
            elif ctrl and k_.lower() == "c" and vis.get("seleccion"):
                copiar_seleccion()
            elif ctrl and k_.lower() == "c" and vis.get("img_sel"):
                copiar_imagenes()
            elif k_ == "Escape" and vis.get("img_sel"):
                vis["img_sel"] = []
                visor_pedir_dibujo()
            elif ctrl and k_.lower() == "a" and v_herr.get() == "Seleccionar":
                seleccionar_pagina(self)
            elif ctrl and k_.lower() in ("c", "x", "v"):
                teclas_paginas(k_.lower())
            elif k_ == "Delete" and vis["comp"] and org.get("sel") and not vis.get("edit_item"):
                org_eliminar()
                for w_ in vistas:
                    w_.lay_k = None
                visor_pedir_dibujo()
            elif k_ in ("Prior", "Left") and not ctrl:
                self.ir(self.pag - 1)
            elif k_ in ("Next", "Right") and not ctrl:
                self.ir(self.pag + 1)
            elif k_ == "Home":
                self.ir(0)
            elif k_ == "End":
                self.ir(10 ** 9)
            elif k_ in ("Up", "Down"):
                self.cv.yview_scroll(-3 if k_ == "Up" else 3, "units")
                self.movido()
            elif k_ == "Escape" and vis["modo_res"]:
                if getattr(self, "_poly", None):
                    self._poly = None
                    self.cv.delete("previa")
                    v_estado.set("Polilínea cancelada.")
                else:
                    alternar_resaltar()

    vistas = [VistaDoc(0), VistaDoc(1)]
    for v_ in vistas:
        v_.cv.configure(cursor="xterm")  # arranca en Seleccionar
    vistas[0].marco.grid(row=0, column=0, sticky="nsew")

    def vista_activa():
        for v_ in vistas:
            if v_.es_activa() and v_.marco.winfo_ismapped():
                return v_
        return vistas[0]

    def visor_pedir_dibujo(*_):
        for v_ in vistas:
            v_.pedir()

    def visor_dibujar(*_):
        for v_ in vistas:
            v_.dibujar()

    def redibujar_todo(*_):
        """v2.5: vuelve a dibujar el visor y las miniaturas (al volver a mostrarse la ventana)."""
        vis["ult"] = vis["ult_mini"] = None
        visor_dibujar()
        mini_dibujar()

    # v3.0: en Windows los procesos que dibujan tardan en arrancar; mientras tanto, la hoja que se ve
    # la dibuja la ventana misma (una por vez, sin trabarla), asi el PDF aparece enseguida
    ayuda = {"docs": {}, "orden": [], "hechos": set(), "job": None}

    def soltar_ayuda(ruta=None):
        for r_ in list(ayuda["docs"]):
            if ruta is None or r_ == ruta:
                try:
                    ayuda["docs"].pop(r_).close()
                    ayuda["orden"].remove(r_)
                except Exception:
                    pass

    def ayudar_render():
        ayuda["job"] = None
        if vis.get("render_listo") or app.get("cerrando"):
            return
        for k_, ruta, pag, z, rot, parar, fol_, tr in list(vis["ult"] or []):
            if k_ in vis["cache"] or k_ in ayuda["hechos"]:
                continue
            ayuda["hechos"].add(k_)
            try:
                d_ = _abrir_cache(ayuda["docs"], ayuda["orden"], ruta, maximo=3)
                img = dibujar_trozo(d_[pag], d_[pag].get_displaylist(annots=True), z, rot, parar, fol_, tr)
                vis["cache"][k_] = ImageTk.PhotoImage(img)
                vis["lru"].append(k_)
                if len(vis["cache"]) == 1:
                    _tiempo("primera hoja (dibujada por la ventana)")
                vis["ult"] = None
                visor_pedir_dibujo()
            except Exception:
                pass
            ayuda["job"] = raiz.after(10, ayudar_render)
            return

    def enviar_pedidos():
        lista = list(vistas[0].ult) + (list(vistas[1].ult) if vis["comp"] else [])
        if lista != vis["ult"]:
            vis["ult"] = lista
            q_pag.put(("ver", lista))
            if not vis.get("render_listo") and ayuda["job"] is None:
                ayuda["job"] = raiz.after(1, ayudar_render)
        while len(vis["lru"]) > CACHE_TROZOS:
            vis["cache"].pop(vis["lru"].pop(0), None)

    def sincronizar(origen):
        """Comparar con «Desplazar juntas»: la otra vista sigue a la misma pagina."""
        if not vis["comp"] or not v_juntas.get() or origen.bloq:
            return
        otra = vistas[1 - origen.lado]
        if not otra.lay:
            return
        p_, f_ = origen.posicion()
        otra.bloq = True
        try:
            otra.ir_pos(p_, f_)
            otra.pedir()
        finally:
            otra.bloq = False

    # ================= miniaturas de la pestana activa
    def mini_dibujar(*_):
        vis["mjob"] = None
        if app["pagina"] != "visor" or not panel_min.winfo_ismapped():
            return
        cvm.configure(bg=col("tarjeta"))
        cvm.delete("all")
        t_ = pest_activa()
        pags = paginas_de(t_) if (t_ and medidas_listas(t_)) else []
        pend_ = giros_pendientes()
        if pend_:  # v3.3: las miniaturas tambien muestran las paginas giradas sin guardar
            pags = [(r_, p_, (g_ + pend_.get((r_, p_), 0)) % 360) for r_, p_, g_ in pags]
        n = len(pags)
        Wm, Hm = max(cvm.winfo_width(), 100), max(cvm.winfo_height(), 100)
        cvm.configure(scrollregion=(0, 0, Wm, max(Hm, n * MINI_CELDA + 10)))
        if not n:
            return
        parar = bool(V["girar_prev"].get())
        y0 = cvm.canvasy(0)
        i0 = max(0, int(y0 // MINI_CELDA) - 1)
        i1 = min(n - 1, int((y0 + Hm) // MINI_CELDA) + 1)
        actual_ = vista_activa().pag if vista_activa().t is t_ else t_.get("pag", 0)
        sel = org["sel"] if org.get("orden") else set()
        busq = vis["busq"] if (vis["busq"] and vis["busq"]["tab"] == t_["id"]) else None
        multi = len(org.get("fuentes") or []) > 1
        pedidos = []
        for i in range(i0, i1 + 1):
            ruta, pag, rot = pags[i]
            y = 6 + i * MINI_CELDA
            cx = Wm // 2
            es_act, es_sel = i == actual_, i in sel
            if es_sel or es_act:
                cvm.create_rectangle(8, y, Wm - 8, y + MINI_CELDA - 8, fill=col("lat_sel") if es_sel else col("suave"),
                                     outline=col("acento") if es_act else "", width=2)
            vw, vh = dims_vista(vis["med"][ruta][pag], rot, parar)
            z = MINI_TAM / max(vw, vh, 1)
            k_ = ("m", ruta, pag, rot, parar, ver_arch(ruta))
            ft = vis["mcache"].get(k_)
            cy = y + 6 + MINI_TAM // 2
            if ft is not None:
                cvm.create_image(cx, cy, image=ft)
                cvm.create_rectangle(cx - ft.width() // 2, cy - ft.height() // 2, cx + ft.width() // 2,
                                     cy + ft.height() // 2, outline=col("borde"))
            else:
                cvm.create_rectangle(cx - vw * z / 2, cy - vh * z / 2, cx + vw * z / 2, cy + vh * z / 2,
                                     fill=col("campo"), outline=col("borde"))
                pedidos.append((k_, ruta, pag, z, rot, parar, None, None))
            if multi:  # color del documento de origen (como en Organizar)
                fid_ = org["fuentes"].index(ruta) if ruta in org["fuentes"] else 0
                cvm.create_rectangle(14, y + MINI_CELDA - 14, Wm - 14, y + MINI_CELDA - 11, outline="",
                                     fill=color_doc(fid_, "barra"))
            if busq and i in busq["por_pos"]:  # punto amarillo: tiene resultados
                cvm.create_oval(Wm - 30, y + 8, Wm - 18, y + 20, fill="#FFC800", outline="#C99A00")
            if vis["res"].get(ruta, {}).get(pag):
                cvm.create_oval(18, y + 8, 30, y + 20, fill="#FFE600", outline="#C9B000")
            cvm.create_text(cx, y + MINI_TAM + 22, text=str(i + 1),
                            fill=col("acento") if (es_act or es_sel) else col("texto2"),
                            font=(FAM, 10, "bold" if es_act else "normal"))
        a_ = vis.get("arr_mini")
        if a_ and a_.get("activo") and a_.get("hueco") is not None:
            yh = 6 + a_["hueco"] * MINI_CELDA - 4
            cvm.create_line(12, yh, Wm - 12, yh, fill=col("acento"), width=4)
        if pedidos != vis["ult_mini"]:
            vis["ult_mini"] = pedidos
            q_min.put(("ver", pedidos + vis.get("imp_ped", [])))
        while len(vis["mlru"]) > CACHE_MINI:
            vis["mcache"].pop(vis["mlru"].pop(0), None)

    def mini_pedir_dibujo(*_):
        if vis["mjob"] is None:
            vis["mjob"] = raiz.after(15, mini_dibujar)

    def mini_ver(i, solo_si_fuera=False):
        t_ = pest_activa()
        if not t_:
            return
        n = len(paginas_de(t_))
        y = 6 + i * MINI_CELDA
        a0, a1 = cvm.canvasy(0), cvm.canvasy(0) + cvm.winfo_height()
        if solo_si_fuera and a0 <= y and y + MINI_CELDA <= a1:
            return
        cvm.yview_moveto(max(0.0, (y - cvm.winfo_height() / 2 + MINI_CELDA / 2) / max(1, n * MINI_CELDA + 10)))
        mini_pedir_dibujo()

    def mini_indice(ev):
        t_ = pest_activa()
        if not t_:
            return None
        i = int(cvm.canvasy(ev.y) - 6) // MINI_CELDA
        return i if 0 <= i < len(paginas_de(t_)) else None

    def mini_press(ev):
        cvm.focus_set()
        i = mini_indice(ev)
        if i is None or not org.get("orden"):
            return
        ctrl, shift = bool(ev.state & 0x4), bool(ev.state & 0x1)
        if shift and org["ancla"] is not None:
            a, b = sorted((org["ancla"], i))
            org["sel"] = set(range(a, b + 1)) | (org["sel"] if ctrl else set())
        elif ctrl:
            org["sel"] ^= {i}
            org["ancla"] = i
        elif i not in org["sel"]:
            org["sel"], org["ancla"] = {i}, i
        vis["arr_mini"] = {"i": i, "x": ev.x_root, "y": ev.y_root, "activo": False, "solo": not ctrl and not shift}
        if not ctrl and not shift:
            vista_activa().ir(i)
        org_info()
        mini_dibujar()

    def widget_pestana(w_):
        """Indice de la pestana bajo el widget (o None)."""
        while w_ is not None:
            k_ = vis["pest_w"].get(str(w_))
            if k_ is not None:
                return k_
            w_ = getattr(w_, "master", None)
        return None

    def mini_motion(ev):
        a_ = vis.get("arr_mini")
        if not a_:
            return
        if not a_["activo"] and abs(ev.x_root - a_["x"]) + abs(ev.y_root - a_["y"]) < 8:
            return
        a_["activo"] = True
        sobre = raiz.winfo_containing(ev.x_root, ev.y_root)
        en_pest = widget_pestana(sobre)
        cvm.configure(cursor="plus" if en_pest is not None else "fleur")
        if sobre is cvm:
            a_["hueco"] = max(0, min(len(org["orden"]), int(round((cvm.canvasy(ev.y) - 6) / MINI_CELDA))))
            if ev.y < 24:
                cvm.yview_scroll(-1, "units")
            elif ev.y > cvm.winfo_height() - 24:
                cvm.yview_scroll(1, "units")
        else:
            a_["hueco"] = None
        if en_pest is not None and en_pest != vis["act"]:
            v_estado.set(f"Soltá para copiar {len(org['sel'])} página(s) a «{pest[en_pest]['nombre']}».")
        mini_dibujar()

    def mini_release(ev):
        a_ = vis.pop("arr_mini", None)
        vis["arr_mini"] = None
        cvm.configure(cursor="")
        if not a_:
            return
        if not a_["activo"]:
            if a_["solo"] and len(org["sel"]) > 1:
                org["sel"] = {a_["i"]}
                mini_dibujar()
            return
        sobre = raiz.winfo_containing(ev.x_root, ev.y_root)
        j = widget_pestana(sobre)
        if j is not None and j != vis["act"]:
            copiar_a_pestana(j)
        elif sobre is cvm and a_.get("hueco") is not None:
            antes = sum(1 for k_ in range(a_["hueco"]) if k_ not in org["sel"])
            org_mover_a(antes)
        mini_dibujar()

    def mini_menu(ev):
        i = mini_indice(ev)
        if i is None or not org.get("orden"):
            return
        if i not in org["sel"]:
            org["sel"], org["ancla"] = {i}, i
            mini_dibujar()
        n_ = len(org["sel"])
        m_ = menu_contextual()
        m_.add_command(label="Ver", command=lambda: vista_activa().ir(i))
        m_.add_separator()
        m_.add_command(label=f"Copiar ({n_})   Ctrl+C", command=org_copiar)
        m_.add_command(label=f"Cortar ({n_})   Ctrl+X", command=lambda: org_copiar(True))
        m_.add_command(label="Pegar después   Ctrl+V", command=org_pegar,
                       state="normal" if org.get("copiado") else "disabled")
        sub = menu_contextual(m_)
        otras = [(k_, t_) for k_, t_ in enumerate(pest) if k_ != vis["act"]]
        for k_, t_ in otras:
            sub.add_command(label=t_["nombre"], command=lambda k__=k_: copiar_a_pestana(k__))
        m_.add_cascade(label="Copiar a otra pestaña", menu=sub, state="normal" if otras else "disabled")
        m_.add_separator()
        m_.add_command(label="Girar ↺", command=lambda: org_girar(-90))
        m_.add_command(label="Girar ↻", command=lambda: org_girar(90))
        m_.add_command(label=f"Eliminar ({n_})   Supr", command=org_eliminar)
        m_.tk_popup(ev.x_root, ev.y_root)

    # ================= v3.5: COMPARANDO, PASAR PAGINAS DE UN PDF A OTRO
    # Cada hoja muestra su numero arriba a la izquierda: clic ahi la elige (Ctrl/Shift: varias), arrastrarla
    # la lleva al otro PDF (o la cambia de lugar en el mismo). Ctrl+C / Ctrl+X / Ctrl+V y Supr tambien sirven.
    def org_lista_sel():
        return [(org["fuentes"][f_], p_, r_) for f_, p_, r_ in (org["orden"][i] for i in sorted(org["sel"])
                                                                if i < len(org["orden"]))]

    def org_insertar(lista, pos=None):
        """Mete en el documento activo las paginas [(ruta, pag, giro)] en 'pos' (por defecto, tras lo elegido)."""
        if not lista:
            return 0
        org_guardar_paso()
        if pos is None:
            pos = (max(org["sel"]) + 1) if org["sel"] else len(org["orden"])
        pos = max(0, min(pos, len(org["orden"])))
        nuevos = []
        for ruta_, p_, r_ in lista:
            if ruta_ not in org["fuentes"]:
                org["fuentes"].append(ruta_)
            nuevos.append((org["fuentes"].index(ruta_), p_, r_))
        org["orden"][pos:pos] = nuevos
        org["sel"] = set(range(pos, pos + len(nuevos)))
        org["ancla"] = pos
        org_dibujar()
        return len(nuevos)

    def insignia_en(v_, ev):
        cx_, cy_ = v_.cv.canvasx(ev.x), v_.cv.canvasy(ev.y)
        for it_ in reversed(v_.cv.find_overlapping(cx_ - 1, cy_ - 1, cx_ + 1, cy_ + 1)):
            for tg_ in v_.cv.gettags(it_):
                if tg_.startswith("ins") and tg_ != "ins":
                    return int(tg_[3:])
        return None

    def pagina_press(v_, i, ev):
        ctrl, shift = bool(ev.state & 0x4), bool(ev.state & 0x1)
        if shift and org.get("ancla") is not None:
            a, b = sorted((org["ancla"], i))
            org["sel"] = set(range(a, b + 1))
        elif ctrl:
            org["sel"] ^= {i}
            org["ancla"] = i
        elif i not in org["sel"]:
            org["sel"], org["ancla"] = {i}, i
        vis["pag_clic"] = (v_.t["id"], i)
        v_._parr = {"i": i, "x": ev.x_root, "y": ev.y_root, "activo": False, "solo": not ctrl and not shift}
        n_ = len(org["sel"])
        v_estado.set(f"{n_} página(s) elegida(s) · arrastrala al otro PDF (copia; con Shift la mueve) · "
                     "Ctrl+C copia · Ctrl+X corta · Ctrl+V pega · Supr quita.")
        visor_pedir_dibujo()
        mini_pedir_dibujo()

    def vista_bajo(xr, yr):
        for v_ in vistas:
            c_ = v_.cv
            if (v_.t is not None and c_.winfo_ismapped() and c_.winfo_rootx() <= xr < c_.winfo_rootx() + c_.winfo_width()
                    and c_.winfo_rooty() <= yr < c_.winfo_rooty() + c_.winfo_height()):
                return v_
        return None

    def hueco_vista(v_, xr, yr):
        lay = v_.lay
        if not lay or not lay["pags"]:
            return 0
        cx_ = v_.cv.canvasx(xr - v_.cv.winfo_rootx())
        cy_ = v_.cv.canvasy(yr - v_.cv.winfo_rooty())
        i = v_.pagina_en(cy_, cx_)
        if fila_multiple(lay, i):  # v3.6: miniaturas: antes o despues segun el lado
            if cx_ > lay["xs"][i] + lay["ws"][i] / 2:
                i += 1
        elif cy_ > lay["ys"][i] + lay["hs"][i] / 2:
            i += 1
        return max(0, min(len(lay["pags"]), i))

    def fila_multiple(lay, i):
        ys = lay["ys"]
        return (i + 1 < len(ys) and ys[i + 1] == ys[i]) or (i > 0 and ys[i - 1] == ys[i])

    def guia_paginas(v_, pos):
        for w_ in vistas:
            w_.cv.delete("guia_p")
        if v_ is None or not v_.lay or not v_.lay["pags"]:
            return
        lay = v_.lay
        n = len(lay["pags"])
        k_ = min(pos, n - 1)
        if fila_multiple(lay, k_) or (pos > 0 and fila_multiple(lay, pos - 1)):  # v3.6: raya vertical
            if pos < n and (pos == 0 or lay["ys"][pos - 1] == lay["ys"][pos]):
                xl, y0, y1 = lay["xs"][pos] - ESPACIO_V / 2, lay["ys"][pos], lay["ys"][pos] + lay["hs"][pos]
            else:
                j_ = pos - 1
                xl, y0, y1 = lay["xs"][j_] + lay["ws"][j_] + ESPACIO_V / 2, lay["ys"][j_], lay["ys"][j_] + lay["hs"][j_]
            v_.cv.create_line(xl, y0 - 6, xl, y1 + 6, fill=col("acento"), width=6, capstyle="round", tags="guia_p")
            return
        yl = lay["ys"][k_] - ESPACIO_V / 2 if pos < n else lay["ys"][n - 1] + lay["hs"][n - 1] + ESPACIO_V / 2
        x0, x1 = lay["xs"][k_] - 10, lay["xs"][k_] + lay["ws"][k_] + 10
        v_.cv.create_line(x0, yl, x1, yl, fill=col("acento"), width=5, capstyle="round", tags="guia_p")
        v_.cv.create_text(x0 + 8, yl - 12, anchor="w", text=f"aquí  (antes de la {pos + 1})" if pos < n else "al final",
                          fill=col("acento"), font=(FAM, 10, "bold"), tags="guia_p")

    def agrandar_hoja(v_, ev):
        """Doble clic en una miniatura: se ve grande (entera); otro doble clic vuelve a las miniaturas."""
        base_ = v_._punto_pagina(v_.cv.canvasx(ev.x), v_.cv.canvasy(ev.y))
        i = base_[0] if base_ else v_.pag
        v_._parr = None
        previo = getattr(v_, "_zoom_mini", None)
        if previo is not None:
            v_._zoom_mini = None
            v_.zoom = previo
        else:
            v_._zoom_mini = v_.zoom
            v_.zoom = "Página entera"
        v_.v_zoom.set(f"{v_.zoom:g} %" if isinstance(v_.zoom, float) else v_.zoom)
        v_.reanclar = False
        v_.lay_k = None
        v_.ir(i)
        v_estado.set("Doble clic de nuevo para volver a las miniaturas." if v_._zoom_mini is not None else
                     "Miniaturas · Ctrl+rueda o − / + las agranda o achica · doble clic agranda una hoja.")

    def pagina_motion(v_, ev):
        a = v_._parr
        if not a["activo"] and abs(ev.x_root - a["x"]) + abs(ev.y_root - a["y"]) < 8:
            return
        a["activo"] = True
        v_.cv.configure(cursor="fleur")
        dst = vista_bajo(ev.x_root, ev.y_root)
        if dst is not None:
            yy = ev.y_root - dst.cv.winfo_rooty()
            if yy < 40:
                dst.cv.yview_scroll(-1, "units")
                dst.movido()
            elif yy > dst.cv.winfo_height() - 40:
                dst.cv.yview_scroll(1, "units")
                dst.movido()
        guia_paginas(dst, hueco_vista(dst, ev.x_root, ev.y_root) if dst else 0)

    def pagina_release(v_, ev):
        a = v_._parr
        v_._parr = None
        v_.cv.configure(cursor=cursor_herramienta())
        for w_ in vistas:
            w_.cv.delete("guia_p")
        if not a["activo"]:
            if a["solo"] and len(org["sel"]) > 1:
                org["sel"] = {a["i"]}
                visor_pedir_dibujo()
            return
        dst = vista_bajo(ev.x_root, ev.y_root)
        if dst is None or not org["sel"]:
            return
        pos = hueco_vista(dst, ev.x_root, ev.y_root)
        if dst is v_ or dst.t is v_.t:
            antes = sum(1 for k_ in range(pos) if k_ not in org["sel"])
            org_mover_a(antes)
            v_estado.set("Páginas movidas · «Guardar» (Ctrl+S) deja el PDF así · Ctrl+Z deshace.")
            return
        mover = bool(ev.state & 0x1)
        lista = org_lista_sel()
        if mover:
            if len(lista) >= len(org["orden"]):
                messagebox.showinfo(NOMBRE, "El PDF tiene que quedar con al menos una página.")
                return
            org_eliminar()
        org["sel"] = set()  # en el de origen ya no queda nada elegido
        dst.activar()
        n_ = org_insertar(lista, pos)
        vis["pag_clic"] = (dst.t["id"], pos)
        v_estado.set(f"{n_} página(s) {'movidas' if mover else 'copiadas'} a «{dst.t['nombre']}» · "
                     "«Guardar» (Ctrl+S) lo deja así · Ctrl+Z deshace.")
        for w_ in vistas:
            w_.lay_k = None
        visor_pedir_dibujo()
        mini_pedir_dibujo()

    def teclas_paginas(k_):
        if not org.get("orden"):
            return
        if not org["sel"]:  # sin seleccion: la pagina donde se hizo clic (o la que se ve)
            v_ = vista_activa()
            pc_ = vis.get("pag_clic")
            p_ = pc_[1] if (pc_ and v_ and v_.t and pc_[0] == v_.t["id"]) else v_.pag
            p_ = max(0, min(p_, len(org["orden"]) - 1))
            org["sel"], org["ancla"] = {p_}, p_
        if k_ == "c":
            org_copiar()
        elif k_ == "x":
            org_copiar(True)
        elif k_ == "v":
            org_pegar()
        if vis["comp"]:
            n_ = len(org.get("copiado") or [])
            v_estado.set({"c": f"{n_} página(s) copiadas: hacé clic en el otro PDF y Ctrl+V.",
                          "x": f"{n_} página(s) cortadas: hacé clic en el otro PDF y Ctrl+V.",
                          "v": "Páginas pegadas · «Guardar» (Ctrl+S) lo deja así · Ctrl+Z deshace."}[k_])
            for w_ in vistas:
                w_.lay_k = None
            visor_pedir_dibujo()

    def mini_teclas(ev):
        ctrl = bool(ev.state & 0x4)
        k_ = ev.keysym.lower()
        n = len(org.get("orden") or [])
        if not n:
            return
        if k_ == "delete":
            org_eliminar()
        elif ctrl and k_ == "z" and ev.state & 0x1:
            org_rehacer()
        elif ctrl and k_ == "z":
            org_deshacer()
        elif ctrl and k_ == "y":
            org_rehacer()
        elif ctrl and k_ == "a":
            org["sel"] = set(range(n))
            mini_dibujar()
        elif ctrl and k_ in ("c", "x", "v"):
            teclas_paginas(k_)
        elif k_ in ("up", "down", "prior", "next"):
            base = (max(org["sel"]) if k_ in ("down", "next") else min(org["sel"])) if org["sel"] else vista_activa().pag
            i = max(0, min(n - 1, base + (1 if k_ in ("down", "next") else -1)))
            if ctrl and k_ in ("up", "down"):
                org_paso(-1 if k_ == "up" else 1)
            else:
                org["sel"], org["ancla"] = {i}, i
                vista_activa().ir(i)
            mini_ver(i, solo_si_fuera=True)
            mini_dibujar()
        elif k_ in ("return", "space") and org["sel"]:
            vista_activa().ir(min(org["sel"]))

    class MenuPdfol:
        """Menu del clic derecho con el estilo de PdFOL (claro y oscuro). Misma forma de uso que tk.Menu:
        add_command / add_separator / add_cascade / tk_popup."""
        abierto = None

        def __init__(self, padre=None):
            self.items = []

        def add_command(self, label="", command=None, state="normal", acelerador="", punto=None, **_):
            if "   " in label and not acelerador:  # «Copiar (2)   Ctrl+C» -> texto y atajo
                label, acelerador = label.split("   ", 1)
            self.items.append(("cmd", label.strip(), command, state != "disabled", acelerador.strip(), punto))

        def add_separator(self):
            self.items.append(("sep",))

        def add_titulo(self, texto):
            self.items.append(("tit", texto))

        def add_cascade(self, label="", menu=None, state="normal", **_):
            self.items.append(("sub", label, menu, state != "disabled" and menu is not None and menu.items, "▸", None))

        def cerrar(self, *_):
            for s_ in getattr(self, "sombras", None) or []:
                try:
                    s_.destroy()
                except Exception:
                    pass
            self.sombras = []
            w = getattr(self, "w", None)
            if w is not None:
                try:
                    w.grab_release()
                    w.destroy()
                except Exception:
                    pass
                self.w = None
            if MenuPdfol.abierto is self:
                MenuPdfol.abierto = None

        def tk_popup(self, x, y):
            # v4.2: menu moderno (como Windows 11): iconos de linea, realce en pastilla, sombra de Windows,
            # aparece con un fundido suave y se ubica en el MONITOR donde esta el programa
            if MenuPdfol.abierto is not None:
                MenuPdfol.abierto.cerrar()
            MenuPdfol.abierto = self
            self.sombras = []
            w = tk.Toplevel(raiz)
            self.w = w
            w.withdraw()
            w.overrideredirect(True)
            w.attributes("-topmost", True)

            def hx(c_):
                c_ = c_.lstrip("#")
                return tuple(int(c_[k:k + 2], 16) for k in (0, 2, 4))

            def mezcla(a_, b_, t_):
                a_, b_ = hx(a_), hx(b_)
                return "#%02X%02X%02X" % tuple(round(a_[k] * t_ + b_[k] * (1 - t_)) for k in range(3))
            oscuro = modo_oscuro()
            fondo = col("tarjeta")
            if oscuro:  # en oscuro, el menu un poco mas claro que el programa (se ve "por encima")
                fondo = mezcla("#FFFFFF", fondo, 0.05)
            txt_c, txt2 = col("texto"), col("texto2")
            acento, linea = col("acento"), col("linea")
            borde = mezcla("#FFFFFF", fondo, 0.14) if oscuro else mezcla(col("borde"), fondo, 0.9)
            w.configure(bg=borde)
            rojo = "#F87171" if oscuro else "#DC2626"
            f_txt = tkfont.Font(root=raiz, family=FAM, size=10)
            f_ata = tkfont.Font(root=raiz, family=FAM, size=9)
            f_tit = tkfont.Font(root=raiz, family=FAM, size=9, weight="bold")
            ALTO, SEP, TIT, PAD = px(34), px(9), px(30), px(5)
            filas, yy = [], PAD
            ancho_txt = ancho_ata = 0
            for it in self.items:
                if it[0] == "sep":
                    filas.append((it, yy, SEP))
                    yy += SEP
                elif it[0] == "tit":
                    filas.append((it, yy, TIT))
                    yy += TIT
                    ancho_txt = max(ancho_txt, f_tit.measure(it[1].upper()) - px(30))
                else:
                    filas.append((it, yy, ALTO))
                    yy += ALTO
                    ancho_txt = max(ancho_txt, f_txt.measure(it[1]))
                    if it[4]:
                        ancho_ata = max(ancho_ata, f_ata.measure(it[4]))
            W = max(px(248), px(46) + ancho_txt + px(30) + ancho_ata + px(16))
            H = yy + PAD
            cv_ = tk.Canvas(w, width=W, height=H, bg=fondo, highlightthickness=0, bd=0, cursor="arrow")
            cv_.pack(padx=1, pady=1)
            estado = {"i": None}
            activos = [k_ for k_, (it, _y, _h) in enumerate(filas) if it[0] in ("cmd", "sub") and it[3]]

            def redondeado(x0, y0, x1, y1, r, **kw):
                pts = [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1, x1 - r, y1, x0 + r, y1,
                       x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]
                return cv_.create_polygon(pts, smooth=True, **kw)

            def pintar():
                cv_.delete("fila")
                for k_, (it, y0, h_) in enumerate(filas):
                    if it[0] == "sep":
                        cv_.create_line(px(12), y0 + h_ / 2, W - px(12), y0 + h_ / 2, fill=linea, tags="fila")
                        continue
                    if it[0] == "tit":  # encabezado del grupo, en versalitas
                        cv_.create_text(px(14), y0 + h_ / 2 + px(2), text=it[1].upper(), anchor="w", font=f_tit,
                                        fill=txt2, tags="fila")
                        continue
                    _t, texto, _acc, activo, atajo, punto = it
                    sobre = estado["i"] == k_ and activo
                    peligro = punto in ("#EF4444", "#DC2626", "#F87171")
                    c_tx = (rojo if peligro else txt_c) if activo else mezcla(txt2, fondo, 0.6)
                    c_ic = (rojo if peligro else (acento if sobre else txt2)) if activo else mezcla(txt2, fondo, 0.45)
                    if sobre:  # pastilla con un toque del color de acento
                        redondeado(px(5), y0 + px(1), W - px(5), y0 + h_ - px(1), px(7),
                                   fill=mezcla(rojo if peligro else acento, fondo, 0.16 if oscuro else 0.11),
                                   outline="", tags="fila")
                        if not peligro:
                            c_tx = txt_c
                    cy = y0 + h_ / 2
                    clave = icono_para(texto) if not getattr(self, "_iconos", {}).get(texto) else self._iconos[texto]
                    if punto and not peligro and clave is None:  # color propio de la opcion (resaltar con color)
                        cv_.create_oval(px(20) - px(5), cy - px(5), px(20) + px(5), cy + px(5), fill=punto, outline="",
                                        tags="fila")
                    else:
                        icono_menu(cv_, clave, px(20), cy, px(7), c_ic, w=max(1.2, px(1.5)))
                    cv_.create_text(px(40), cy, text=texto, anchor="w", font=f_txt, fill=c_tx, tags="fila")
                    if atajo and _t == "cmd":
                        cv_.create_text(W - px(14), cy, text=atajo, anchor="e", font=f_ata,
                                        fill=mezcla(txt2, fondo, 0.85), tags="fila")
                    elif _t == "sub":
                        icono_flecha = W - px(16)
                        cv_.create_line(icono_flecha - px(3), cy - px(4), icono_flecha + px(1), cy, icono_flecha - px(3),
                                        cy + px(4), fill=txt2, width=max(1.2, px(1.5)), capstyle="round", tags="fila")
            pintar()

            def indice(y_):
                for k_, (it, y0, h_) in enumerate(filas):
                    if y0 <= y_ < y0 + h_ and it[0] in ("cmd", "sub"):
                        return k_
                return None

            def mover(ev):
                k_ = indice(ev.y)
                if k_ != estado["i"]:
                    estado["i"] = k_
                    cv_.configure(cursor="hand2" if k_ is not None and filas[k_][0][3] else "arrow")
                    pintar()

            def ejecutar(k_):
                if k_ is None:
                    return "break"
                it, y0, h_ = filas[k_]
                _t, _texto, accion, activo, _a, _p = it
                if not activo:
                    return "break"
                if _t == "sub":  # el submenu se abre al costado
                    xs, ys = w.winfo_rootx() + W - px(6), w.winfo_rooty() + y0 - PAD
                    self.cerrar()
                    raiz.after(10, lambda: accion.tk_popup(xs, ys))
                    return "break"
                self.cerrar()
                if accion:
                    raiz.after(10, accion)
                return "break"

            def teclas(ev):
                if not activos:
                    return
                if ev.keysym in ("Down", "Up"):
                    i_ = estado["i"]
                    pos = activos.index(i_) if i_ in activos else -1
                    pos = (pos + (1 if ev.keysym == "Down" else -1)) % len(activos)
                    estado["i"] = activos[pos]
                    pintar()
                elif ev.keysym in ("Return", "KP_Enter", "space"):
                    ejecutar(estado["i"])
            cv_.bind("<Motion>", mover)
            cv_.bind("<Leave>", lambda e: (estado.update(i=None), pintar()))
            cv_.bind("<ButtonRelease-1>", lambda e: ejecutar(indice(e.y)))
            w.bind("<Key>", teclas)
            w.update_idletasks()
            ww, hh = W + 2, H + 2
            # en el monitor donde se hizo clic (no en la pantalla principal)
            a0, b0, a1, b1 = area_monitor(x, y, w)
            if x + ww > a1 - 4:
                x = max(a0 + 4, x - ww)
            if y + hh > b1 - 4:
                y = max(b0 + 4, b1 - hh - 4)
            x, y = max(a0 + 2, x), max(b0 + 2, y)
            w.geometry(f"{ww}x{hh}+{x}+{y}")
            alfa_ok = os.name == "nt"
            if alfa_ok:
                try:
                    w.attributes("-alpha", 0.0)
                except Exception:
                    alfa_ok = False
            w.deiconify()
            w.lift()
            esquinas_redondeadas(w)  # Windows 11: esquinas redondeadas
            if not sombra_nativa(w) and os.name == "nt":  # sin la sombra de Windows: una suave propia
                try:
                    s_ = tk.Toplevel(raiz)
                    s_.overrideredirect(True)
                    s_.configure(bg="#000000")
                    s_.attributes("-alpha", 0.09)
                    s_.geometry(f"{ww + 6}x{hh + 6}+{x - 2}+{y + 2}")
                    esquinas_redondeadas(s_)
                    self.sombras.append(s_)
                    w.lift()
                except Exception:
                    pass
            if alfa_ok:  # aparece con un fundido corto (y baja un poquito)
                def fundido(k_=1):
                    if self.w is not w:
                        return
                    try:
                        w.attributes("-alpha", min(1.0, k_ / 5))
                        w.geometry(f"+{x}+{y - 5 + k_}")
                    except Exception:
                        return
                    if k_ < 5:
                        w.after(16, lambda: fundido(k_ + 1))
                fundido()
            w.bind("<Escape>", self.cerrar)

            def afuera(ev):
                x0, y0 = w.winfo_rootx(), w.winfo_rooty()
                if not (x0 <= ev.x_root <= x0 + w.winfo_width() and y0 <= ev.y_root <= y0 + w.winfo_height()):
                    self.cerrar()
            w.bind("<ButtonPress>", afuera, add="+")
            w.after(30, lambda: (w.focus_force(), w.grab_set()) if self.w is w else None)

    def menu_contextual(padre=None):
        return MenuPdfol(padre)

    def alternar_miniaturas():
        if app.get("lado_izq") == "marcadores":  # v3.0: desde marcadores vuelve a las miniaturas
            app["lado_izq"] = "minis"
            almacen.datos["miniaturas"] = True
        else:
            almacen.datos["miniaturas"] = almacen.datos.get("miniaturas") is False
        almacen.guardar()
        columna_izquierda()
        raiz.after(30, mini_dibujar)
        visor_pedir_dibujo()

    # ---------- v3.0: marcadores (indice del PDF) en la columna izquierda
    panel_toc = ctk.CTkScrollableFrame(col_izq, fg_color=C["tarjeta"], corner_radius=12, border_width=1,
                                       border_color=C["borde"], scrollbar_button_color=C["suave_h"],
                                       scrollbar_button_hover_color=C["borde"])
    toc_estado = {"ruta": None}

    def dibujar_toc():
        t_ = pest_activa()
        ruta = t_["ruta"] if t_ else None
        if ruta == toc_estado["ruta"] and panel_toc.winfo_children():
            return
        toc_estado["ruta"] = ruta
        for w_ in panel_toc.winfo_children():
            w_.destroy()
        ctk.CTkLabel(panel_toc, text="Marcadores", font=F(13, "bold"), text_color=C["texto"], anchor="w").pack(
            fill="x", padx=8, pady=(6, 4))
        toc = []
        if ruta:
            try:
                with fitz.open(ruta) as d_:
                    toc = d_.get_toc(simple=True)
            except Exception:
                toc = []
        if not toc:
            ctk.CTkLabel(panel_toc, text="Este PDF no tiene marcadores.", font=F(11), text_color=C["texto2"],
                         anchor="w", justify="left", wraplength=ANCHO_IZQ - 40).pack(fill="x", padx=8)
            return
        for nivel, tit, pag in toc[:400]:
            ctk.CTkButton(panel_toc, text=("   " * (nivel - 1)) + tit, anchor="w", font=F(11), height=26,
                          corner_radius=6, fg_color="transparent", hover_color=C["suave"], text_color=C["texto"],
                          command=lambda r_=ruta, p_=pag - 1: ir_a_pagina_de(r_, p_)).pack(fill="x", padx=2)

    def ir_a_pagina_de(ruta, pag):
        v_ = vista_activa()
        t_ = pest_activa()
        if not v_ or not t_:
            return
        for k_, (r_, p_, _g) in enumerate(paginas_de(t_)):
            if r_ == ruta and p_ == pag:
                v_.ir(k_)
                return

    def alternar_marcadores():
        app["lado_izq"] = "minis" if app.get("lado_izq") == "marcadores" else "marcadores"
        if app["lado_izq"] == "minis" and almacen.datos.get("miniaturas") is False:
            almacen.datos["miniaturas"] = True
        columna_izquierda()
        raiz.after(30, mini_dibujar)
        visor_pedir_dibujo()

    PANEL_DE_OPC = {"fol": "foliar", "apl": "aplanar", "comp": "comprimir"}

    def pintar_chips_org(*_):
        for cl_, b_ in chips_org.items():
            on_ = bool(V[cl_].get())
            b_.configure(fg_color=C["acento"] if on_ else C["suave"], text_color="#FFFFFF" if on_ else C["texto"],
                         text=("  ✓  " if on_ else "  ○  ") + {"fol": "Foliar", "apl": "Aplanar", "comp": "Comprimir"}[cl_]
                         + ("   · ajustes ›" if on_ else ""))

    def chip_org(cl_):
        panel_ = PANEL_DE_OPC[cl_]
        if V[cl_].get() and app.get("panel") == panel_:
            V[cl_].set(False)  # ya estaba activa y a la vista: se apaga
            cerrar_panel()
        else:
            V[cl_].set(True)
            abrir_panel(panel_)
        pintar_chips_org()

    for cl_o, b_o in chips_org.items():
        b_o.configure(command=lambda c__=cl_o: chip_org(c__))
        V[cl_o].trace_add("write", pintar_chips_org)

    def columna_izquierda():
        """Columna izquierda: miniaturas o marcadores en el visor (si estan visibles) o el documento activo;
        abajo, «Proceso» (v3.0: en el visor, solo con Aplanar, Foliar o Comprimir abiertos)."""
        en_visor = app["pagina"] == "visor"
        t_ = pest_activa()
        v_doc_nom.set(t_["nombre"] if t_ else "Ningún documento abierto")
        con_proceso = (not en_visor) or app.get("panel") in ("aplanar", "foliar", "comprimir")
        if app["pagina"] == "organizar":
            caja_opc_org.grid(row=1, column=0, sticky="ew", padx=10, pady=(0, 4))
            pintar_chips_org()
        else:
            caja_opc_org.grid_remove()
        if con_proceso:
            inferior.grid(row=2, column=0, sticky="sew", pady=(8, 0))
        else:
            inferior.grid_remove()
        if en_visor:
            riel.grid()
        else:
            riel.grid_remove()
        lado = app.get("lado_izq", "minis")
        visibles = almacen.datos.get("miniaturas") is not False
        if en_visor and not pest:
            col_izq.grid_remove()  # en el inicio sin documento, la columna no hace falta
        else:
            col_izq.grid()
        if en_visor and visibles and lado == "marcadores":
            tarj_doc.grid_remove()
            panel_min.grid_remove()
            panel_toc.grid(row=0, column=0, rowspan=2, sticky="nsew")
            dibujar_toc()
        elif en_visor and visibles:
            tarj_doc.grid_remove()
            panel_toc.grid_remove()
            panel_min.grid(row=0, column=0, rowspan=2, sticky="nsew")
        elif en_visor:
            tarj_doc.grid_remove()
            panel_min.grid_remove()
            panel_toc.grid_remove()
            if not con_proceso:
                col_izq.grid_remove()
        else:
            panel_toc.grid_remove()
            panel_min.grid_remove()
            tarj_doc.grid(row=0, column=0, sticky="new")
            if app["pagina"] == "organizar":
                caja_org_izq.pack(fill="x", padx=2, pady=(0, 2))
            else:
                caja_org_izq.pack_forget()

    raiz.after_idle(columna_izquierda)
    for ev_ in ("<MouseWheel>", "<Button-4>", "<Button-5>"):
        cvm.bind(ev_, lambda e: (cvm.yview_scroll(-3 if (getattr(e, "num", 0) == 4 or getattr(e, "delta", 0) > 0)
                                                  else 3, "units"), mini_pedir_dibujo()))
    cvm.bind("<ButtonPress-1>", mini_press)
    cvm.bind("<B1-Motion>", mini_motion)
    cvm.bind("<ButtonRelease-1>", mini_release)
    cvm.bind("<Button-3>", mini_menu)
    cvm.bind("<Key>", mini_teclas)
    cvm.bind("<Configure>", lambda e: mini_pedir_dibujo())

    # ================= copiar paginas entre pestanas
    def copiar_a_pestana(j):
        if not org.get("orden") or not org["sel"] or not 0 <= j < len(pest) or j == vis["act"]:
            return
        items = [(org["fuentes"][f_], p_, r_) for f_, p_, r_ in (org["orden"][i] for i in sorted(org["sel"]))]
        t_ = pest[j]
        o_ = t_.setdefault("org", {})
        if not o_.get("orden"):  # la otra pestana todavia no tenia el orden armado
            n_ = len(vis["med"].get(t_["ruta"]) or []) or contar_paginas(t_["ruta"])
            o_.update(fuentes=[t_["ruta"]], orden=[(0, k_, 0) for k_ in range(n_)], sel=set(), ancla=None,
                      pila=[], ruta=t_["ruta"], original=[(0, k_, 0) for k_ in range(n_)], origen={})
        o_["pila"] = (o_.get("pila") or []) + [(list(o_["orden"]), set(o_.get("sel") or set()))]
        o_["fuentes"] = list(o_["fuentes"])
        nuevos = []
        for ruta, p_, r_ in items:
            if ruta not in o_["fuentes"]:
                o_["fuentes"].append(ruta)
            nuevos.append((o_["fuentes"].index(ruta), p_, r_))
        o_["orden"] = list(o_["orden"]) + nuevos
        t_["orgver"] = t_.get("orgver", 0) + 1
        v_estado.set(f"{len(items)} página(s) copiadas al final de «{t_['nombre']}».")
        dibujar_pestanas()
        visor_pedir_dibujo()

    # ================= busqueda (Ctrl+F) y resaltado
    def enfocar_busqueda(*_):
        if app["pagina"] != "visor":
            mostrar_pagina("visor")
        e_buscar.focus_set()
        e_buscar.select_range(0, "end")
        return "break"

    def buscar_texto(texto):
        t_ = pest_activa()
        texto = texto.strip()
        if not t_ or not texto:
            return
        b_ = vis["busq"]
        if b_ and b_["texto"] == texto and b_["tab"] == t_["id"] and b_["ver"] == version_de(t_):
            busq_mover(1)
            return
        if not medidas_listas(t_):
            v_estado.set("Esperá a que termine de abrir el documento.")
            return
        vis["nbusq"] += 1
        vis["busq"] = {"id": vis["nbusq"], "texto": texto, "tab": t_["id"], "ver": version_de(t_), "hits": [],
                       "por_pos": {}, "i": -1, "fin": False, "hechas": 0, "total": 0}
        asegurar_buscador()
        q_bus.put(("buscar", vis["nbusq"], texto, [(r_, p_) for r_, p_, _g in paginas_de(t_)]))
        busq_mostrar()

    def busq_mostrar():
        b_ = vis["busq"]
        if not b_:
            caja_busq.pack_forget()
            return
        n = len(b_["hits"])
        if not b_["fin"]:
            txt = f"«{b_['texto']}»: buscando… {n} hasta ahora ({b_['hechas']} de {b_['total'] or '…'} págs.)"
        elif not n:
            txt = f"«{b_['texto']}»: sin resultados"
        else:
            txt = f"«{b_['texto']}»: {b_['i'] + 1} de {n}"
        v_busq.set(txt)
        if not caja_busq.winfo_ismapped():
            caja_busq.pack(side="left", padx=(10, 0))

    def busq_mover(d):
        b_ = vis["busq"]
        if not b_ or not b_["hits"]:
            return
        b_["i"] = (b_["i"] + d) % len(b_["hits"])
        pos, r_ = b_["hits"][b_["i"]]
        v_ = vista_activa()
        v_.ver_rect(pos, r_)
        mini_ver(pos, solo_si_fuera=True)
        busq_mostrar()
        mini_dibujar()

    def busq_cerrar():
        if vis["busq"]:
            q_bus.put(("parar",))
        vis["busq"] = None
        busq_mostrar()
        visor_pedir_dibujo()
        mini_pedir_dibujo()

    def resaltar_resultados():
        b_ = vis["busq"]
        t_ = pest_activa()
        if not b_ or not b_["hits"] or not t_:
            return
        pags = paginas_de(t_)
        por_pag = {}
        for pos, r_ in b_["hits"]:
            ruta, pag, _g = pags[pos]
            por_pag.setdefault((ruta, pag), []).append(r_)
        for (ruta, pag), rects in por_pag.items():
            for r_ in rects:
                nuevo_resaltado(ruta, pag, "texto", rects=[r_], refrescar_=False)
        v_estado.set(f"{len(b_['hits'])} resultados resaltados. «Guardar resaltados» (Ctrl+S) los deja en el PDF.")
        actualizar_resaltes()

    # ---------- resaltador: barra flotante (modo, colores, opacidad)
    COLORES_RES = ["#FFD600", "#4FC878", "#5AAAFA", "#EC4899", "#FB923C", "#A78BFA", "#EF4444", "#94A3B8"]
    pref_res = almacen.datos.get("resaltador") or {}
    v_res_modo = tk.StringVar(value=pref_res.get("modo", "Texto") if pref_res.get("modo") in ("Texto", "Área", "Libre")
                              else "Texto")
    v_res_op = tk.DoubleVar(value=float(pref_res.get("op", 0.4)))
    vis["res_color"] = tuple(pref_res.get("color", (255, 214, 0)))
    vis["capas_it"] = {}
    vis["chars"] = {}
    vis["nres"] = 0
    res_bar = ctk.CTkFrame(area_doc, fg_color=C["tarjeta"], corner_radius=14, border_width=1, border_color=C["borde"])
    seg_res = segmentado(res_bar, ["Texto", "Área", "Libre"], v_res_modo, cmd=lambda v_: cambiar_modo_res())
    seg_res.pack(side="left", padx=(10, 8), pady=8)
    ctk.CTkFrame(res_bar, width=1, height=22, fg_color=C["borde"]).pack(side="left", padx=4)
    botones_res = []
    for hx in COLORES_RES:
        b_ = ctk.CTkButton(res_bar, text="", width=22, height=22, corner_radius=11, fg_color=hx, hover_color=hx,
                           border_width=0, border_color=C["acento"], command=lambda h_=hx: poner_color_res(_hex(h_)))
        b_.pack(side="left", padx=3)
        botones_res.append((b_, _hex(hx)))
    b_res_otro = ctk.CTkButton(res_bar, text="Otro…", width=56, height=24, corner_radius=12, font=F(11),
                               fg_color=C["suave"], hover_color=C["suave_h"], text_color=C["texto"],
                               command=lambda: color_res_otro())
    b_res_otro.pack(side="left", padx=(8, 4))
    ctk.CTkFrame(res_bar, width=1, height=22, fg_color=C["borde"]).pack(side="left", padx=4)
    ctk.CTkLabel(res_bar, text="Opacidad", font=F(11), text_color=C["texto2"]).pack(side="left", padx=(4, 4))
    ctk.CTkSlider(res_bar, from_=0.15, to=0.85, variable=v_res_op, width=90, height=16, button_color=C["acento"],
                  button_hover_color=C["acento_h"], progress_color=C["acento"], fg_color=C["suave"],
                  command=lambda _v: guardar_pref_res()).pack(side="left", padx=(0, 6))
    ctk.CTkButton(res_bar, text="✕", width=28, height=28, corner_radius=14, font=F(13), fg_color="transparent",
                  hover_color=C["suave_h"], text_color=C["texto2"], command=lambda: alternar_resaltar()).pack(
        side="left", padx=(2, 8))

    def guardar_pref_res():
        almacen.datos["resaltador"] = {"modo": v_res_modo.get(), "color": list(vis["res_color"]),
                                       "op": round(float(v_res_op.get()), 2)}
        almacen.guardar()

    def marcar_color_res():
        for b_, rgb in botones_res:
            b_.configure(border_width=3 if tuple(rgb) == tuple(vis["res_color"]) else 0)

    def poner_color_res(rgb):
        vis["res_color"] = tuple(int(v_) for v_ in rgb)
        marcar_color_res()
        guardar_pref_res()
        if not vis["modo_res"]:
            activar_resaltador(v_res_modo.get())

    def color_res_otro():
        res_ = colorchooser.askcolor(color="#%02x%02x%02x" % tuple(vis["res_color"]), title="Color del resaltado")
        if res_ and res_[0]:
            poner_color_res(res_[0])

    CURSOR_RES = {"Texto": "xterm", "Área": "crosshair", "Libre": "pencil"}
    AYUDA_RES = {"Texto": "Resaltar texto: arrastrá sobre las letras (se marca solo el texto, letra por letra).",
                 "Área": "Resaltar área: arrastrá para un rectángulo, o hacé clics para una polilínea "
                         "(doble clic, Enter o clic en el primer punto la cierra).",
                 "Libre": "Resaltar a mano alzada: dibujá con el mouse."}

    def cambiar_modo_res():
        for v_ in vistas:
            v_.cerrar_poligono() if getattr(v_, "_poly", None) else None
            v_.cv.configure(cursor=cursor_herramienta())
        guardar_pref_res()
        if vis["modo_res"]:
            v_estado.set(AYUDA_RES[v_res_modo.get()] + " Esc termina.")

    def activar_resaltador(modo=None):
        if modo:
            v_res_modo.set(modo)
        if not vis["modo_res"]:
            alternar_resaltar()
        else:
            cambiar_modo_res()

    def alternar_resaltar(*_):
        vis["modo_res"] = not vis["modo_res"]
        b_resaltar.configure(fg_color=C["acento"] if vis["modo_res"] else C["suave"],
                             text_color="#FFFFFF" if vis["modo_res"] else C["texto"])
        if vis["modo_res"]:
            res_bar.place(relx=0.5, y=46, anchor="n")
            res_bar.lift()
            marcar_color_res()
        else:
            res_bar.place_forget()
            for v_ in vistas:
                v_._poly = None
                v_.cv.delete("previa")
        cambiar_modo_res()
        if not vis["modo_res"]:
            v_estado.set("Listo.")

    def caracteres_de(ruta, pag):
        """Letras de la pagina [(x0, y0, x1, y1, renglon, letra)] o None si todavia se estan leyendo."""
        k_ = (ruta, pag, ver_arch(ruta))
        if k_ in vis["chars"]:
            return vis["chars"][k_]
        if ("pedido",) + k_ not in vis["chars"]:
            vis["chars"][("pedido",) + k_] = True
            asegurar_buscador()
            q_bus.put(("caracteres", ruta, pag, ver_arch(ruta)))
        return None

    def char_cercano(chars, p_):
        px, py = p_
        mejor, dmin = 0, 1e18
        for k_, (x0, y0, x1, y1, _l, _c) in enumerate(chars):
            dx = 0 if x0 <= px <= x1 else min(abs(px - x0), abs(px - x1))
            dy = 0 if y0 <= py <= y1 else min(abs(py - y0), abs(py - y1))
            d_ = dx + dy * 4
            if d_ < dmin:
                mejor, dmin = k_, d_
                if d_ == 0:
                    break
        return mejor

    def rects_seleccion(chars, a_, b_):
        """Un rectangulo por renglon con las letras de a_ a b_ (inclusive)."""
        res, act_, lin = [], None, None
        for x0, y0, x1, y1, l_, c_ in chars[a_:b_ + 1]:
            if l_ != lin:
                if act_:
                    res.append(tuple(act_))
                act_, lin = fitz.Rect(x0, y0, x1, y1), l_
            else:
                act_ |= fitz.Rect(x0, y0, x1, y1)
        if act_:
            res.append(tuple(act_))
        return [r_ for r_ in res if fitz.Rect(r_).width > 0.5]

    def imagen_item(item, M):
        """Imagen RGBA del resaltado (en pantalla) y su esquina (x, y) relativa a la pagina."""
        if item["tipo"] in ("firma", "texto_n", "reemplazo"):
            return imagen_edicion(item, M)
        rgba = tuple(item["color"]) + (int(255 * float(item["op"])),)
        z = abs(M.a) + abs(M.b)
        if item["tipo"] in ("texto", "rect"):
            rs = [fitz.Rect(r_) * M for r_ in item["rects"]]
            caja = fitz.Rect(rs[0])
            for r_ in rs[1:]:
                caja |= r_
            pad = 1
        else:
            ps = [fitz.Point(p_) * M for p_ in item["pts"]]
            pad = max(2, item.get("ancho", 2) * z / 2 + 2) if item["tipo"] == "libre" else 2
            caja = fitz.Rect(min(p_.x for p_ in ps), min(p_.y for p_ in ps), max(p_.x for p_ in ps),
                             max(p_.y for p_ in ps))
        bx, by = int(caja.x0 - pad), int(caja.y0 - pad)
        w_, h_ = max(1, int(caja.width + 2 * pad) + 1), max(1, int(caja.height + 2 * pad) + 1)
        img = Image.new("RGBA", (w_, h_), (0, 0, 0, 0))
        msk = Image.new("L", (w_, h_), 0)
        d_ = ImageDraw.Draw(msk)
        if item["tipo"] in ("texto", "rect"):
            for r_ in rs:
                d_.rounded_rectangle([r_.x0 - bx, r_.y0 - by, r_.x1 - bx, r_.y1 - by], radius=2, fill=255)
        elif item["tipo"] == "poli":
            d_.polygon([(p_.x - bx, p_.y - by) for p_ in ps], fill=255)
        else:
            ancho = max(1, int(item.get("ancho", 2) * z))
            d_.line([(p_.x - bx, p_.y - by) for p_ in ps], fill=255, width=ancho, joint="curve")
            for p_ in (ps[0], ps[-1]):
                d_.ellipse([p_.x - bx - ancho / 2, p_.y - by - ancho / 2, p_.x - bx + ancho / 2, p_.y - by + ancho / 2],
                           fill=255)
        img.paste(Image.new("RGBA", (w_, h_), rgba), (0, 0), msk)
        return bx, by, img

    def capa_item(item, M, clave_m):
        k_ = (item["id"], item.get("ver", 0), clave_m)
        v_ = vis["capas_it"].get(k_)
        if v_ is None:
            if len(vis["capas_it"]) > 400:
                vis["capas_it"].clear()
            bx, by, img = imagen_item(item, M)
            v_ = vis["capas_it"][k_] = (bx, by, ImageTk.PhotoImage(img))
        return v_

    def item_contiene(item, p_):
        if item["tipo"] == "giro":
            return False
        p_ = fitz.Point(p_)
        if item["tipo"] in ("firma", "texto_n", "reemplazo"):
            return fitz.Rect(caja_texto(item)).contains(p_)
        if item["tipo"] in ("texto", "rect"):
            return any(fitz.Rect(r_).contains(p_) for r_ in item["rects"])
        xs_ = [q[0] for q in item["pts"]]
        ys_ = [q[1] for q in item["pts"]]
        m_ = item.get("ancho", 4)
        return min(xs_) - m_ <= p_.x <= max(xs_) + m_ and min(ys_) - m_ <= p_.y <= max(ys_) + m_

    def nuevo_resaltado(ruta, pag, tipo, rects=None, pts=None, ancho=None, refrescar_=True):
        guardar_historia()
        vis["nres"] += 1
        item = {"id": vis["nres"], "tipo": tipo, "color": tuple(vis["res_color"]), "op": round(float(v_res_op.get()), 2)}
        if rects is not None:
            item["rects"] = [tuple(r_) for r_ in rects]
        if pts is not None:
            item["pts"] = [tuple(p_) for p_ in pts]
        if ancho is not None:
            item["ancho"] = float(ancho)
        vis["res"].setdefault(ruta, {}).setdefault(pag, []).append(item)
        vis["res_pila"].append((ruta, pag, item))
        if refrescar_:
            actualizar_resaltes()
            v_estado.set(f"{n_resaltes()} resaltado(s) sin guardar · Ctrl+Z deshace · Ctrl+S los guarda en el PDF.")

    def agregar_resaltado(ruta, pag, r_):  # (compatibilidad) un rectangulo de texto
        nuevo_resaltado(ruta, pag, "texto", rects=[r_])

    def quitar_resaltado(ruta, pag, item):
        lista = vis["res"].get(ruta, {}).get(pag, [])
        if item in lista:
            guardar_historia()
            lista.remove(item)
        vis["res_pila"] = [x for x in vis["res_pila"] if x[2] is not item]
        actualizar_resaltes()

    # ---- v2.7: deshacer / rehacer todo (resaltados, firmas y textos: agregar, mover, estilo, quitar)
    hist = {"atras": [], "adelante": [], "ult": None, "t": 0.0}

    def tocar(it_):
        vis["nver"] = vis.get("nver", 0) + 1
        it_["ver"] = vis["nver"]

    def guardar_historia(tipo=None, ident=None):
        ahora = time.time()
        if tipo and hist["ult"] == (tipo, ident) and ahora - hist["t"] < 1.2:
            hist["t"] = ahora  # varios cambios seguidos del mismo texto: un solo paso
            return
        hist["ult"], hist["t"] = (tipo, ident), ahora
        hist["atras"].append(copy.deepcopy(vis["res"]))
        del hist["atras"][:-80]
        hist["adelante"].clear()

    def limpiar_historia():
        hist["atras"].clear()
        hist["adelante"].clear()
        hist["ult"] = None

    def _poner_foto(foto):
        e_ = vis.get("edit_item")
        vis["res"] = foto
        vis["res_pila"] = sorted(((r_, p_, it_) for r_, ps_ in foto.items() for p_, l_ in ps_.items() for it_ in l_),
                                 key=lambda x: x[2]["id"])
        vis["edit_item"] = None
        if e_:
            for x in vis["res_pila"]:
                if x[2]["id"] == e_[2]["id"]:
                    vis["edit_item"] = x
                    break
        hist["ult"] = None
        vis["ult"] = vis["ult_mini"] = None
        actualizar_resaltes()
        e_ = vis.get("edit_item")
        if e_ and e_[2]["tipo"] in ("texto_n", "reemplazo"):
            sincronizar_panel(e_[2])
        n_ = n_resaltes()
        v_estado.set(f"{n_} cambio(s) sin guardar · Ctrl+Z deshace · Ctrl+Y rehace." if n_ else "Sin cambios pendientes.")

    def deshacer_edicion():
        if not hist["atras"]:
            v_estado.set("No hay nada para deshacer.")
            return False
        hist["adelante"].append(copy.deepcopy(vis["res"]))
        _poner_foto(hist["atras"].pop())
        return True

    def rehacer_edicion():
        if not hist["adelante"]:
            v_estado.set("No hay nada para rehacer.")
            return False
        hist["atras"].append(copy.deepcopy(vis["res"]))
        _poner_foto(hist["adelante"].pop())
        return True

    def duplicar_editado():
        e_ = vis.get("edit_item")
        if not e_ or e_[2]["tipo"] not in ("firma", "texto_n"):
            v_estado.set("Elegí un texto agregado, una firma o un sello para duplicarlo.")
            return
        it_ = copy.deepcopy(e_[2])
        it_.pop("id", None)
        r_ = fitz.Rect(it_["rect"]) + (14, 14, 14, 14)
        it_["rect"] = tuple(r_)
        agregar_item(e_[0], e_[1], it_)

    def mover_editado(dx, dy):
        e_ = vis.get("edit_item")
        if not e_ or e_[2]["tipo"] not in ("firma", "texto_n"):
            return False
        guardar_historia("mover", e_[2]["id"])
        e_[2]["rect"] = tuple(fitz.Rect(e_[2]["rect"]) + (dx, dy, dx, dy))
        tocar(e_[2])
        visor_pedir_dibujo()
        mini_pedir_dibujo()
        return True

    def deshacer_resaltado():
        if vis["res_pila"]:
            ruta, pag, item = vis["res_pila"].pop()
            quitar_resaltado(ruta, pag, item)

    def cursor_herramienta():
        if app.get("panel") == "firmar" and not vis["modo_res"]:
            return "tcross"
        if app.get("panel") == "texto" and not vis["modo_res"]:
            return "xterm"
        if vis["modo_res"]:
            return CURSOR_RES[v_res_modo.get()]
        return "xterm" if v_herr.get() == "Seleccionar" else "hand2"

    def cambiar_herramienta():
        if vis["modo_res"]:
            alternar_resaltar()  # elegir Seleccionar o Mano sale del resaltador
        for v_ in vistas:
            v_.cv.configure(cursor=cursor_herramienta())
        v_estado.set("Seleccionar: arrastrá sobre el texto para copiarlo (Ctrl+C). Doble clic: palabra, triple: renglón."
                     if v_herr.get() == "Seleccionar" else "Mano: arrastrá para mover la hoja.")

    def texto_seleccion():
        sel_ = vis.get("seleccion")
        if not sel_:
            return ""
        chars = caracteres_de(sel_["base"][1], sel_["base"][2]) or []
        a_, b_ = sorted((sel_["a"], sel_["b"]))
        partes, lin = [], None
        for c_ in chars[a_:b_ + 1]:
            if lin is not None and c_[4] != lin:
                partes.append("\n")
            partes.append(c_[5])
            lin = c_[4]
        return "".join(partes)

    # ================= v3.4: COPIAR IMAGENES DEL PDF (se pegan como archivo en el Explorador, o en Word, WhatsApp…)
    cache_imgs = {}

    def imagenes_de(ruta, pag):
        """Imagenes de la pagina: [{'bbox': rect en coordenadas de la hoja, 'xref', 'tr': matriz como se ve}]."""
        k_ = (ruta, pag, ver_arch(ruta))
        if k_ not in cache_imgs:
            out = []
            try:
                with fitz.open(ruta) as d_:
                    pg = d_[pag]
                    rm = pg.rotation_matrix
                    area_ = abs(pg.rect)
                    for inf in pg.get_image_info(xrefs=True):
                        r_ = fitz.Rect(inf["bbox"]) * rm
                        if r_.is_empty or r_.width < 6 or r_.height < 6 or abs(r_) > area_ * 4:
                            continue
                        out.append({"ruta": ruta, "pag": pag, "bbox": tuple(r_), "xref": inf.get("xref", 0),
                                    "tr": tuple(fitz.Matrix(inf["transform"]) * rm)})
            except Exception:
                out = []
            if len(cache_imgs) > 60:
                cache_imgs.clear()
            cache_imgs[k_] = out
        return cache_imgs[k_]

    def imagen_en(ruta, pag, p_, sin_fondo=False):
        p_ = fitz.Point(p_)
        dentro = [im_ for im_ in imagenes_de(ruta, pag) if fitz.Rect(im_["bbox"]).contains(p_)]
        if sin_fondo and dentro:  # v4.1: la imagen de toda la hoja (escaneo) no se elige con un clic
            try:
                with fitz.open(ruta) as d_:
                    area = abs(d_[pag].rect)
                dentro = [im_ for im_ in dentro if abs(fitz.Rect(im_["bbox"])) < area * 0.85]
            except Exception:
                pass
        return dentro[-1] if dentro else None  # la de mas arriba

    def misma_img(a_, b_):
        return a_["ruta"] == b_["ruta"] and a_["pag"] == b_["pag"] and a_["bbox"] == b_["bbox"]

    def elegir_imagen(im_, sumar=False):
        lista = list(vis.get("img_sel") or [])
        ya = next((x for x in lista if misma_img(x, im_)), None)
        if sumar:
            if ya:
                lista.remove(ya)
            else:
                lista.append(im_)
        else:
            lista = [im_]
        vis["img_sel"] = lista
        if lista:
            v_estado.set(f"{len(lista)} imagen(es) elegida(s) · Ctrl+C la copia: pegala en una carpeta, Word, "
                         "WhatsApp… · Ctrl+clic suma otra.")
        visor_pedir_dibujo()

    def _orientar(img, tr):
        """La imagen tal como se ve en la hoja (girada o espejada como la puso el PDF)."""
        a, b, c, d = tr[:4]
        esq = {(u, v): (u * a + v * c, u * b + v * d) for u in (0, 1) for v in (0, 1)}
        xs_ = [q[0] for q in esq.values()]
        ys_ = [q[1] for q in esq.values()]
        mx, my, Mx = min(xs_), min(ys_), max(xs_)
        tl = min(esq, key=lambda k: abs(esq[k][0] - mx) + abs(esq[k][1] - my))
        tr_ = min(esq, key=lambda k: abs(esq[k][0] - Mx) + abs(esq[k][1] - my))
        if (tl, tr_) == ((0, 0), (1, 0)):
            return img, False
        prueba = Image.new("L", (2, 2))
        prueba.putdata([0, 1, 2, 3])  # (0,0) (1,0) (0,1) (1,1)
        nombre_ = {0: (0, 0), 1: (1, 0), 2: (0, 1), 3: (1, 1)}
        T_ = Image.Transpose
        for op in (T_.FLIP_LEFT_RIGHT, T_.FLIP_TOP_BOTTOM, T_.ROTATE_90, T_.ROTATE_180, T_.ROTATE_270, T_.TRANSPOSE,
                   T_.TRANSVERSE):
            q_ = prueba.transpose(op)
            if (nombre_[q_.getpixel((0, 0))], nombre_[q_.getpixel((1, 0))]) == (tl, tr_):
                return img.transpose(op), True
        return img, False

    def extraer_imagen(s_):
        """-> (bytes del archivo, extension, imagen PIL). Se usa la imagen original (mejor calidad)."""
        with fitz.open(s_["ruta"]) as d_:
            pg = d_[s_["pag"]]
            datos, ext, img = None, "png", None
            if s_["xref"]:
                try:
                    inf = d_.extract_image(s_["xref"])
                    datos, ext = inf["image"], inf["ext"].lower()
                    if inf.get("smask") or ext not in ("jpeg", "jpg", "png") or inf.get("colorspace", 3) >= 4:
                        pix = fitz.Pixmap(d_, s_["xref"])
                        if inf.get("smask"):
                            try:
                                pix = fitz.Pixmap(pix, fitz.Pixmap(d_, inf["smask"]))
                            except Exception:
                                pass
                        if pix.colorspace and pix.colorspace.n not in (1, 3):
                            pix = fitz.Pixmap(fitz.csRGB, pix)
                        datos, ext = pix.tobytes("png"), "png"
                    img = Image.open(io.BytesIO(datos))
                    img.load()
                    img, girada = _orientar(img, s_["tr"])
                    if girada:
                        b_ = io.BytesIO()
                        if ext in ("jpeg", "jpg"):
                            img.convert("RGB").save(b_, "JPEG", quality=95)
                        else:
                            img.save(b_, "PNG")
                        datos = b_.getvalue()
                except Exception:
                    img = None
            if img is None:  # imagen metida en el contenido: se recorta de la hoja en alta resolucion
                pix = pg.get_pixmap(dpi=220, clip=fitz.Rect(s_["bbox"]), alpha=False)
                datos, ext = pix.tobytes("png"), "png"
                img = Image.open(io.BytesIO(datos))
                img.load()
        return datos, ("jpg" if ext == "jpeg" else ext), img

    def _portapapeles_windows(rutas, img=None):
        import ctypes
        from ctypes import wintypes
        import struct
        u32, k32 = ctypes.WinDLL("user32"), ctypes.WinDLL("kernel32")
        k32.GlobalAlloc.restype = ctypes.c_void_p
        k32.GlobalAlloc.argtypes = [wintypes.UINT, ctypes.c_size_t]
        k32.GlobalLock.restype = ctypes.c_void_p
        k32.GlobalLock.argtypes = [ctypes.c_void_p]
        k32.GlobalUnlock.argtypes = [ctypes.c_void_p]
        k32.GlobalFree.argtypes = [ctypes.c_void_p]
        u32.OpenClipboard.argtypes = [wintypes.HWND]
        u32.SetClipboardData.restype = ctypes.c_void_p
        u32.SetClipboardData.argtypes = [wintypes.UINT, ctypes.c_void_p]
        u32.RegisterClipboardFormatW.restype = wintypes.UINT
        u32.RegisterClipboardFormatW.argtypes = [wintypes.LPCWSTR]

        def poner(fmt, datos):
            h_ = k32.GlobalAlloc(0x0042, len(datos))  # GHND
            p_ = k32.GlobalLock(h_)
            ctypes.memmove(p_, datos, len(datos))
            k32.GlobalUnlock(h_)
            if not u32.SetClipboardData(fmt, h_):
                k32.GlobalFree(h_)
                raise OSError("SetClipboardData")
        hwnd = raiz.winfo_id()
        for _ in range(20):  # otro programa puede estar usando el portapapeles un instante
            if u32.OpenClipboard(hwnd):
                break
            time.sleep(0.03)
        else:
            raise OSError("El portapapeles está ocupado por otro programa.")
        try:
            u32.EmptyClipboard()
            lista = ("\0".join(rutas) + "\0\0").encode("utf-16-le")
            poner(15, struct.pack("<IiiII", 20, 0, 0, 0, 1) + lista)  # CF_HDROP: archivos (Explorador)
            poner(u32.RegisterClipboardFormatW("Preferred DropEffect"), struct.pack("<I", 5))  # copiar
            if img is not None:  # CF_DIB: la imagen (Word, WhatsApp, Paint…)
                b_ = io.BytesIO()
                fondo_ = img
                if img.mode in ("RGBA", "LA", "P"):
                    fondo_ = Image.new("RGB", img.size, (255, 255, 255))
                    im_rgba = img.convert("RGBA")
                    fondo_.paste(im_rgba, mask=im_rgba.split()[-1])
                fondo_.convert("RGB").save(b_, "BMP")
                poner(8, b_.getvalue()[14:])
        finally:
            u32.CloseClipboard()

    def guardar_imagenes(lista, carpeta):
        """Escribe las imagenes en 'carpeta' y devuelve [(ruta_archivo, imagen PIL)]."""
        hechos, usados = [], set()
        for k_, s_ in enumerate(lista, 1):
            datos, ext, img = extraer_imagen(s_)
            base = os.path.splitext(os.path.basename(original_de(s_["ruta"])))[0]
            nom = f"{base}_pag{s_['pag'] + 1}_imagen{k_}.{ext}"
            while nom.lower() in usados or os.path.exists(os.path.join(carpeta, nom)):
                nom = nom.replace(f".{ext}", f"_.{ext}")
            usados.add(nom.lower())
            r_ = os.path.join(carpeta, nom)
            with open(r_, "wb") as f_:
                f_.write(datos)
            hechos.append((r_, img))
        return hechos

    def copiar_imagenes(lista=None):
        lista = lista or vis.get("img_sel") or []
        if not lista:
            return
        import tempfile
        carpeta = os.path.join(tempfile.gettempdir(), "PdFOL_imagenes", time.strftime("%Y%m%d_%H%M%S"))
        try:
            os.makedirs(carpeta, exist_ok=True)
            hechos = guardar_imagenes(lista, carpeta)
        except Exception as e:
            messagebox.showerror(NOMBRE, f"No se pudo sacar la imagen del PDF:\n{e}")
            return
        rutas = [r_ for r_, _ in hechos]
        if sys.platform.startswith("win"):
            try:
                _portapapeles_windows(rutas, hechos[0][1] if len(hechos) == 1 else None)
            except Exception as e:
                messagebox.showerror(NOMBRE, f"No se pudo copiar al portapapeles:\n{e}")
                return
        else:
            raiz.clipboard_clear()
            raiz.clipboard_append("\n".join(rutas))
        n_ = len(rutas)
        v_estado.set((f"{n_} imágenes copiadas" if n_ > 1 else "Imagen copiada") +
                     " · pegala (Ctrl+V) en una carpeta del Explorador" + (", en Word o WhatsApp." if n_ == 1 else "."))

    def guardar_imagenes_como(lista=None):
        lista = lista or vis.get("img_sel") or []
        if not lista:
            return
        if len(lista) == 1:
            s_ = lista[0]
            try:
                datos, ext, _img = extraer_imagen(s_)
            except Exception as e:
                messagebox.showerror(NOMBRE, f"No se pudo sacar la imagen del PDF:\n{e}")
                return
            base = os.path.splitext(os.path.basename(original_de(s_["ruta"])))[0]
            dest = filedialog.asksaveasfilename(title="Guardar imagen", initialfile=f"{base}_pag{s_['pag'] + 1}.{ext}",
                                                defaultextension="." + ext,
                                                filetypes=[("Imagen", f"*.{ext}"), ("Todos", "*.*")])
            if dest:
                with open(dest, "wb") as f_:
                    f_.write(datos)
                v_estado.set(f"Imagen guardada: {dest}")
            return
        carpeta = filedialog.askdirectory(title=f"Carpeta para las {len(lista)} imágenes")
        if carpeta:
            try:
                guardar_imagenes(lista, carpeta)
                v_estado.set(f"{len(lista)} imágenes guardadas en {carpeta}")
            except Exception as e:
                messagebox.showerror(NOMBRE, f"No se pudieron guardar:\n{e}")

    def copiar_seleccion():
        t_ = texto_seleccion()
        if t_:
            raiz.clipboard_clear()
            raiz.clipboard_append(t_)
            v_estado.set(f"Texto copiado ({len(t_)} caracteres).")

    def resaltar_seleccion():
        sel_ = vis.get("seleccion")
        if not sel_:
            return
        chars = caracteres_de(sel_["base"][1], sel_["base"][2]) or []
        a_, b_ = sorted((sel_["a"], sel_["b"]))
        rects = rects_seleccion(chars, a_, b_)
        if rects:
            nuevo_resaltado(sel_["base"][1], sel_["base"][2], "texto", rects=rects)
        vis["seleccion"] = None
        visor_pedir_dibujo()

    def seleccionar_pagina(vista):
        base = vista._punto_pagina(0, 0, i=vista.pag) if vista.lay else None
        chars = caracteres_de(base[1], base[2]) if base else None
        if chars:
            vis["seleccion"] = {"vista": vista, "base": base, "a": 0, "b": len(chars) - 1}
            visor_pedir_dibujo()
            v_estado.set(f"Página seleccionada ({len(chars)} caracteres) · Ctrl+C copia.")

    def copiar_texto_sel():
        raiz.clipboard_clear()
        raiz.clipboard_append(vis.get("texto_sel") or "")
        v_estado.set("Texto copiado.")

    # ---- v3.3: girar paginas de verdad (se guarda en el PDF con «Guardar», como los demas cambios)
    def giros_pendientes():
        out = {}
        for r_, ps_ in vis["res"].items():
            for p_, l_ in ps_.items():
                g_ = sum(it_.get("grados", 0) for it_ in l_ if it_["tipo"] == "giro") % 360
                if g_:
                    out[(r_, p_)] = g_
        return out

    def girar_paginas(d, todas=False):
        t_ = pest_activa()
        v_ = vista_activa()
        if not t_ or not v_ or not v_.lay:
            v_estado.set("Abrí un PDF para girar sus páginas.")
            return
        if app["pagina"] != "visor":
            mostrar_pagina("visor")
        pags_ = v_.lay["pags"]
        elegidas = range(len(pags_)) if todas else [min(v_.pag, len(pags_) - 1)]
        v_.reanclar = v_.posicion() if v_.lay else None
        guardar_historia()
        for i_ in elegidas:
            ruta, pag, _r = pags_[i_]
            lista = vis["res"].setdefault(ruta, {}).setdefault(pag, [])
            ya = next((it_ for it_ in lista if it_["tipo"] == "giro"), None)
            if ya:
                ya["grados"] = (ya["grados"] + d) % 360
                if not ya["grados"]:
                    lista.remove(ya)
                    vis["res_pila"] = [x for x in vis["res_pila"] if x[2] is not ya]
            else:
                vis["nres"] += 1
                it_ = {"tipo": "giro", "grados": d % 360, "id": vis["nres"], "ver": 0, "op": 1.0, "color": (0, 0, 0),
                       "rect": (0, 0, 0, 0)}
                lista.append(it_)
                vis["res_pila"].append((ruta, pag, it_))
            if not lista:
                vis["res"][ruta].pop(pag, None)
        for v__ in vistas:
            v__.lay_k = None
        vis["ult"] = vis["ult_mini"] = None
        actualizar_resaltes()
        n_ = len(elegidas)
        v_estado.set(("Todo el documento girado" if todas else "Página girada") +
                     " · «Guardar» (Ctrl+S) lo deja así en el PDF · Ctrl+Z deshace.")
        visor_pedir_dibujo()
        mini_pedir_dibujo()
        return n_

    def menu_girar(d):
        lado_ = "derecha" if d > 0 else "izquierda"
        menu_desde(_pos_cinta("girar_der" if d > 0 else "girar_izq"),
                   [(f"Girar esta página a la {lado_}", lambda: girar_paginas(d)),
                    (f"Girar todo el documento a la {lado_}", lambda: girar_paginas(d, True)), ("-", None),
                    (f"Girar solo la vista a la {lado_} (no cambia el PDF)", lambda: girar_vista(d))])

    def n_resaltes(rutas=None):
        return sum(len(l_) for r_, ps in vis["res"].items() if rutas is None or r_ in rutas for l_ in ps.values())

    def refrescar_boton_guardar():
        n = n_resaltes()
        t_ = pest_activa()
        org_ = bool(t_ and tiene_organizado(t_))  # v3.5: tambien paginas copiadas, pegadas o movidas
        if n or org_:
            b_guardar_res.configure(text=f"Guardar cambios ({n})" if n else "Guardar cambios")
            if not b_guardar_res.winfo_ismapped():
                b_guardar_res.pack(side="right", padx=(6, 0))
        elif b_guardar_res.winfo_ismapped():
            b_guardar_res.pack_forget()

    def actualizar_resaltes():
        refrescar_boton_guardar()
        visor_pedir_dibujo()
        mini_pedir_dibujo()

    def original_de(ruta):
        for t_ in pest:
            o_ = org_de(t_)
            if ruta in (o_.get("origen") or {}):
                return o_["origen"][ruta]
        return ruta

    # ---- v3.5: guardar las paginas organizadas (copiadas, pegadas, movidas) desde el visor
    def dialogo_guardar_paginas(t_):
        o_ = org_de(t_)
        w = ctk.CTkToplevel(raiz)
        w.title(f"{NOMBRE} · guardar")
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        ctk.CTkLabel(w, text=f"Guardar «{t_['nombre']}»", font=F(15, "bold"), text_color=C["texto"],
                     anchor="w").pack(fill="x", padx=22, pady=(18, 2))
        n_p, n_f = len(o_.get("orden") or []), len(o_.get("fuentes") or [])
        lin_ = f"Queda con {n_p} páginas" + (f" (con páginas de {n_f - 1} PDF más)" if n_f > 1 else "") + "."
        n_r = n_resaltes(rutas_de(t_))
        if n_r:
            lin_ += f" También {n_r} resaltado(s), firma(s) o texto(s)."
        ctk.CTkLabel(w, text=lin_ + "\n«En este PDF» lo reemplaza con las páginas como las ves. «Como copia» deja "
                                    "el original sin tocar.", font=F(11), text_color=C["texto2"], anchor="w",
                     justify="left", wraplength=430).pack(fill="x", padx=22, pady=(6, 0))
        pie = ctk.CTkFrame(w, fg_color="transparent")
        pie.pack(fill="x", padx=22, pady=16)
        boton(pie, "En este PDF", primario=True, ancho=120,
              command=lambda: (w.destroy(), guardar_paginas(t_, False))).pack(side="right", padx=(8, 0))
        boton(pie, "Como copia…", ancho=120, command=lambda: (w.destroy(), guardar_paginas(t_, True))).pack(
            side="right", padx=(8, 0))
        boton(pie, "Cancelar", ancho=96, command=w.destroy).pack(side="right")
        w.bind("<Escape>", lambda _e: w.destroy())
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + (raiz.winfo_height() - w.winfo_reqheight()) // 3}")
        w.after(100, lambda: (w.grab_set(), w.focus_force()))
        return "break"

    def _armar_esperando(orden_, fuentes_, dest):
        pr = mp.Process(target=armar_organizado, args=(orden_, fuentes_, dest), daemon=True)
        pr.start()
        while pr.is_alive():  # la ventana sigue respondiendo mientras se arma
            raiz.update()
            time.sleep(0.05)
        return pr.exitcode == 0 and os.path.isfile(dest)

    def guardar_paginas(t_, copia):
        o_ = org_de(t_)
        if not o_.get("orden"):
            return
        ruta = t_["ruta"]
        if copia:
            base_ = os.path.splitext(os.path.basename(original_de(ruta)))[0]
            dest = filedialog.asksaveasfilename(title="Guardar copia", initialdir=os.path.dirname(ruta),
                                                initialfile=base_ + "_copia.pdf", defaultextension=".pdf",
                                                filetypes=[("PDF", "*.pdf")])
            if not dest:
                return
            if os.path.normcase(os.path.abspath(dest)) in {os.path.normcase(os.path.abspath(f_)) for f_ in o_["fuentes"]}:
                messagebox.showerror(NOMBRE, "Para reemplazar el mismo PDF usá «En este PDF».")
                return
            v_estado.set(f"Guardando {os.path.basename(dest)}…")
            if _armar_esperando(list(o_["orden"]), list(o_["fuentes"]), dest):
                v_estado.set(f"Copia guardada: {os.path.basename(dest)}")
                v_detalle.set(dest)
            else:
                messagebox.showerror(NOMBRE, f"No se pudo guardar:\n{dest}")
            return
        rutas_t = rutas_de(t_)
        if n_resaltes(rutas_t):  # primero lo dibujado (va en cada PDF de origen, en su pagina)
            guardar_resaltados(False, rutas_t)
            if n_resaltes(rutas_t):
                return
            o_ = org_de(t_)
        orden_, fuentes_ = list(o_["orden"]), list(o_["fuentes"])
        tmp = ruta + ".pdfol_tmp"
        v_estado.set(f"Guardando {t_['nombre']}…")
        if not _armar_esperando(orden_, fuentes_, tmp):
            messagebox.showerror(NOMBRE, f"No se pudo guardar:\n{ruta}")
            return
        # otras pestanas (o lo copiado) que usan paginas de este PDF siguen viendo las de antes
        usa_ = [x for x in pest if x is not t_ and ruta in (org_de(x).get("fuentes") or [])]
        if usa_ or ruta in [c_[0] for c_ in org.get("copiado") or []]:
            import tempfile
            snap = os.path.join(tempfile.gettempdir(), "PdFOL_fuentes",
                                time.strftime("%Y%m%d_%H%M%S_") + os.path.basename(ruta))
            os.makedirs(os.path.dirname(snap), exist_ok=True)
            shutil.copy2(ruta, snap)
            for x in usa_:
                fs_ = org_de(x)["fuentes"]
                fs_[fs_.index(ruta)] = snap
                org_de(x).setdefault("origen", {})[snap] = original_de(ruta)
            org["copiado"] = [((snap if c_[0] == ruta else c_[0]),) + tuple(c_[1:]) for c_ in org.get("copiado") or []]
        soltar_archivo(ruta)
        for _ in range(60):  # Windows: esperar a que todos suelten el archivo
            try:
                os.replace(tmp, ruta)
                break
            except PermissionError:
                raiz.update()
                time.sleep(0.1)
        else:
            messagebox.showerror(NOMBRE, f"El PDF está abierto en otro programa; no se pudo reemplazar:\n{ruta}\n\n"
                                         f"Quedó guardado como:\n{tmp}")
            return
        vis["ver_arch"][ruta] = ver_arch(ruta) + 1
        vis["med"].pop(ruta, None)
        vis["pedida"].discard(ruta)
        cache_imgs.clear()
        n_ = contar_paginas(ruta)
        nuevo = [(0, k, 0) for k in range(n_)]
        datos_ = {"fuentes": [ruta], "orden": nuevo, "sel": set(), "ancla": None, "pila": [], "rehacer": [],
                  "ruta": ruta, "original": list(nuevo), "origen": {}}
        vis["orgver"] += 1
        if t_ is pest_activa():
            org.update(datos_)
            org_reiniciar_cache()
            _abrir_documento(ruta)
            org["ruta"] = ruta
        else:
            t_["org"] = datos_
        t_["orgver"] = vis["orgver"]
        vis["ult"] = vis["ult_mini"] = None
        for w_ in vistas:
            w_.lay_k = None
        medidas_listas(t_)
        dibujar_pestanas()
        visor_pedir_dibujo()
        mini_pedir_dibujo()
        refrescar_boton_guardar()
        v_estado.set(f"«{t_['nombre']}» guardado con {n_} páginas.")

    def guardar_resaltados_dialogo(*_):
        if vis.get("ined"):  # v4.1: lo que se estaba escribiendo en la hoja queda puesto
            ined_terminar(True)
        t_g = pest_activa()
        if t_g and tiene_organizado(t_g) and app["pagina"] == "visor":  # v3.5: paginas copiadas o movidas
            return dialogo_guardar_paginas(t_g)
        if not n_resaltes():
            return "break"
        w = ctk.CTkToplevel(raiz)
        w.title(f"{NOMBRE} · guardar resaltados")
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        rutas = [r_ for r_, ps in vis["res"].items() if any(ps.values())]
        ctk.CTkLabel(w, text=f"Guardar {n_resaltes()} cambio(s)", font=F(15, "bold"), text_color=C["texto"],
                     anchor="w").pack(fill="x", padx=22, pady=(18, 2))
        ctk.CTkLabel(w, text="\n".join(os.path.basename(original_de(r_)) for r_ in rutas), font=F(11),
                     text_color=C["texto2"], anchor="w", justify="left").pack(fill="x", padx=22)
        ctk.CTkLabel(w, text="Resaltados, firmas, sellos y textos. «En este PDF» los agrega al mismo archivo (el "
                             "resto queda igual). «Como copia» deja el original sin tocar.", font=F(11), text_color=C["texto2"],
                     anchor="w", justify="left", wraplength=420).pack(fill="x", padx=22, pady=(8, 0))
        pie = ctk.CTkFrame(w, fg_color="transparent")
        pie.pack(fill="x", padx=22, pady=16)
        boton(pie, "En este PDF", primario=True, ancho=120,
              command=lambda: (w.destroy(), guardar_resaltados(False))).pack(side="right", padx=(8, 0))
        boton(pie, "Como copia…", ancho=120, command=lambda: (w.destroy(), guardar_resaltados(True))).pack(
            side="right", padx=(8, 0))
        boton(pie, "Cancelar", ancho=96, command=w.destroy).pack(side="right")
        w.bind("<Escape>", lambda _e: w.destroy())
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + (raiz.winfo_height() - w.winfo_reqheight()) // 3}")
        w.after(100, lambda: (w.grab_set(), w.focus_force()))
        return "break"

    def guardar_resaltados(copia, rutas=None):
        """Agrega los resaltados como anotaciones de resaltado del PDF."""
        if vis.get("ined"):  # v4.1: lo que se estaba escribiendo en la hoja queda puesto
            ined_terminar(True)
        hechos, errores = 0, []
        for ruta, pags in list(vis["res"].items()):
            if rutas is not None and ruta not in rutas:
                continue
            if not any(pags.values()):
                continue
            orig = original_de(ruta)
            destinos = [orig] + ([ruta] if ruta != orig else [])
            if copia:
                base = os.path.splitext(orig)[0]
                sug = os.path.basename(base) + "_resaltado.pdf"
                dest = filedialog.asksaveasfilename(title="Guardar copia con resaltados", initialdir=os.path.dirname(orig),
                                                    initialfile=sug, defaultextension=".pdf", filetypes=[("PDF", "*.pdf")])
                if not dest:
                    continue
                destinos = [dest]
            for k_, dest in enumerate(destinos):
                try:
                    fuente = orig if (copia or k_ == 0) else ruta
                    soltar_archivo(fuente)
                    d = fitz.open(fuente)
                    con_fuentes = any(it_["tipo"] in ("texto_n", "reemplazo") and "fontfile" in kw_fuente(it_)
                                      for items_ in pags.values() for it_ in items_)
                    hubo_giro = []
                    for pag, items_ in pags.items():
                        pg = d[pag]
                        dm = pg.derotation_matrix
                        editables_ = [it_ for it_ in items_ if it_["tipo"] in ("firma", "texto_n", "reemplazo")]
                        if editables_:
                            guardar_editables(pg, editables_)
                        for it_ in items_:
                            if it_["tipo"] in ("firma", "texto_n", "reemplazo", "giro"):
                                continue
                            c_ = tuple(v_ / 255 for v_ in it_["color"])
                            if it_["tipo"] in ("texto", "rect"):
                                a_ = pg.add_highlight_annot([fitz.Rect(r_) * dm for r_ in it_["rects"]])
                                a_.set_colors(stroke=c_)
                            elif it_["tipo"] == "poli":
                                a_ = pg.add_polygon_annot([tuple(fitz.Point(p_) * dm) for p_ in it_["pts"]])
                                a_.set_colors(stroke=c_, fill=c_)
                                a_.set_border(width=0)
                            else:
                                a_ = pg.add_ink_annot([[tuple(fitz.Point(p_) * dm) for p_ in it_["pts"]]])
                                a_.set_colors(stroke=c_)
                                a_.set_border(width=it_.get("ancho", 6))
                            a_.set_opacity(float(it_["op"]))
                            try:
                                a_.set_blendmode(fitz.PDF_BM_Multiply)  # como marcador: el texto se sigue viendo
                            except Exception:
                                pass
                            a_.update()
                        giro_ = sum(it_.get("grados", 0) for it_ in items_ if it_["tipo"] == "giro") % 360
                        if giro_:  # v3.3: la pagina queda girada en el PDF (despues de poner lo demas)
                            pg.set_rotation((pg.rotation + giro_) % 360)
                            if giro_ % 180:
                                hubo_giro.append(pag)
                    if con_fuentes:  # v2.7: de las fuentes de Windows solo quedan las letras usadas (PDF liviano)
                        try:
                            d.subset_fonts()
                        except Exception:
                            pass
                    if copia:
                        d.save(dest, garbage=3, deflate=True)
                    elif d.can_save_incrementally() and not con_fuentes:
                        d.saveIncr()
                    else:
                        tmp = fuente + ".pdfol_tmp"
                        d.save(tmp, garbage=1, deflate=True)
                        d.close()
                        os.replace(tmp, fuente)
                        d = None
                    if d is not None:
                        d.close()
                    if not copia:
                        vis["ver_arch"][fuente] = ver_arch(fuente) + 1
                        med_ = vis["med"].get(fuente)
                        if hubo_giro and med_:  # las hojas giradas cambian de forma (alto <-> ancho)
                            med_ = list(med_)
                            for pq_ in hubo_giro:
                                if pq_ < len(med_):
                                    med_[pq_] = (med_[pq_][1], med_[pq_][0])
                            vis["med"][fuente] = med_
                            vis["med_ver"] = vis.get("med_ver", 0) + 1
                    hechos += sum(len(r_) for r_ in pags.values()) if k_ == 0 else 0
                except Exception as e:
                    errores.append(f"{os.path.basename(dest)}: {e}")
            if copia or not errores:
                vis["res"].pop(ruta, None)
        vis["res_pila"] = [x for x in vis["res_pila"] if x[0] in vis["res"]]
        limpiar_historia()
        vis["ult"] = vis["ult_mini"] = None
        limpiar_historia()
        actualizar_resaltes()
        if errores:
            messagebox.showerror(NOMBRE, "No se pudieron guardar algunos resaltados:\n\n" + "\n".join(errores))
        elif hechos:
            v_estado.set(f"{hechos} cambio(s) guardados " + ("en la copia." if copia else "en el PDF."))

    # ================= v2.6: firmas, sellos y texto (se dibujan como los resaltados y se guardan con ellos)
    EDITABLES = ("firma", "texto_n", "reemplazo")
    cache_firma = {}

    def clave_cat(cat=None):
        return "sellos" if (cat or v_fcat.get()) == "Sellos" else "firmas"

    def lista_firmas(cat=None):
        k_ = clave_cat(cat)
        d_ = carpeta_firmas()
        lista = [n_ for n_ in almacen.datos.get(k_, []) if os.path.isfile(os.path.join(d_, n_))]
        almacen.datos[k_] = lista
        return lista

    def firma_elegida(cat=None):
        lista = lista_firmas(cat)
        ult = almacen.datos.get(clave_cat(cat)[:-1] + "_ult")
        return ult if ult in lista else (lista[0] if lista else None)

    def miniatura_firma(nombre, w_=120, h_=56):
        k_ = ("mini", nombre, modo_oscuro())
        if k_ not in cache_firma:
            try:
                im_ = Image.open(os.path.join(carpeta_firmas(), nombre)).convert("RGBA")
                im_.thumbnail((w_ * 2, h_ * 2), Image.LANCZOS)
                fondo_ = Image.new("RGBA", (w_ * 2, h_ * 2), (255, 255, 255, 255))
                dch = ImageDraw.Draw(fondo_)
                for yy in range(0, h_ * 2, 12):  # cuadritos: se ve que el fondo es transparente
                    for xx in range(0, w_ * 2, 12):
                        if (xx // 12 + yy // 12) % 2:
                            dch.rectangle([xx, yy, xx + 11, yy + 11], fill=(232, 236, 241, 255))
                fondo_.alpha_composite(im_, ((w_ * 2 - im_.width) // 2, (h_ * 2 - im_.height) // 2))
                cache_firma[k_] = ctk.CTkImage(fondo_, size=(w_, h_))
            except Exception:
                cache_firma[k_] = None
        return cache_firma[k_]

    def dibujar_firmas_panel():
        if caja_firmas is None:
            return
        for w_ in caja_firmas.winfo_children():
            w_.destroy()
        lista = lista_firmas()
        sel_ = firma_elegida()
        que = "sellos" if clave_cat() == "sellos" else "firmas"
        if not lista:
            ctk.CTkLabel(caja_firmas, text=f"Todavía no hay {que}. Agregá una desde una foto o imagen escaneada.",
                         font=F(12), text_color=C["texto2"], anchor="w", justify="left", wraplength=380).pack(
                anchor="w", pady=6)
        for k_, n_ in enumerate(lista):
            celda = ctk.CTkFrame(caja_firmas, fg_color="transparent")
            celda.grid(row=k_ // 2, column=k_ % 2, padx=6, pady=6, sticky="w")
            b_ = ctk.CTkButton(celda, text="", image=miniatura_firma(n_), width=132, height=66, corner_radius=10,
                               fg_color="transparent", hover_color=C["suave"], border_width=2,
                               border_color=C["acento"] if n_ == sel_ else C["borde"],
                               command=lambda n2=n_: elegir_firma(n2))
            b_.pack(side="left")
            ctk.CTkButton(celda, text="✕", width=24, height=24, corner_radius=12, font=F(11), fg_color=C["suave"],
                          hover_color=C["suave_h"], text_color=C["texto2"],
                          command=lambda n2=n_: borrar_firma(n2)).pack(side="left", padx=(4, 0), anchor="n")
        if b_agregar_firma is not None:
            b_agregar_firma.configure(state="normal" if len(lista) < MAX_FIRMAS else "disabled")
        v_firma_info.set(f"{len(lista)} de {MAX_FIRMAS} {que} guardados/as. "
                         + ("Se usa la marcada (la última que usaste)." if lista else "")
                         + (" Para agregar otra, borrá una." if len(lista) >= MAX_FIRMAS else ""))

    def elegir_firma(nombre):
        almacen.datos[clave_cat()[:-1] + "_ult"] = nombre
        almacen.guardar()
        dibujar_firmas_panel()
        v_estado.set("Hacé clic en la hoja donde va.")

    def borrar_firma(nombre):
        if not messagebox.askyesno(NOMBRE, "¿Borrar esta " + ("firma" if clave_cat() == "firmas" else "imagen de sello")
                                   + " guardada?\n\n(Lo que ya está guardado en tus PDF no cambia.)"):
            return
        k_ = clave_cat()
        almacen.datos[k_] = [n_ for n_ in almacen.datos.get(k_, []) if n_ != nombre]
        almacen.guardar()
        dibujar_firmas_panel()

    def agregar_firma_dialogo():
        if len(lista_firmas()) >= MAX_FIRMAS:
            return
        r_ = filedialog.askopenfilename(title="Elegí la imagen de la " + ("firma" if clave_cat() == "firmas" else "sello"),
                                        filetypes=[("Imágenes", "*.png *.jpg *.jpeg *.bmp *.webp *.tif *.tiff"),
                                                   ("Todos", "*.*")])
        if not r_:
            return
        try:
            original = Image.open(r_)
            original.load()
        except Exception:
            messagebox.showerror(NOMBRE, "No se pudo abrir esa imagen.")
            return
        w = ctk.CTkToplevel(raiz)
        w.title(f"{NOMBRE} · " + ("firma" if clave_cat() == "firmas" else "sello") + " desde imagen")
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        est = {"res": None}
        v_quitar = tk.BooleanVar(value=True)
        v_int = tk.DoubleVar(value=50)
        ctk.CTkLabel(w, text="Vista previa (los cuadritos son lo transparente)", font=F(13, "bold"),
                     text_color=C["texto"], anchor="w").pack(fill="x", padx=20, pady=(16, 6))
        l_prev = ctk.CTkLabel(w, text="", width=440, height=220, fg_color=C["campo"], corner_radius=10)
        l_prev.pack(padx=20)
        fila_ = ctk.CTkFrame(w, fg_color="transparent")
        fila_.pack(fill="x", padx=20, pady=(10, 0))
        ctk.CTkCheckBox(fila_, text="Quitar el fondo claro", variable=v_quitar, font=F(12), text_color=C["texto"],
                        fg_color=C["acento"], hover_color=C["acento_h"], border_color=C["texto2"], checkbox_width=18,
                        checkbox_height=18, border_width=2, command=lambda: actualizar()).pack(side="left")
        ctk.CTkLabel(fila_, text="Intensidad", font=F(12), text_color=C["texto2"]).pack(side="left", padx=(18, 6))
        ctk.CTkSlider(fila_, from_=0, to=100, variable=v_int, width=150, button_color=C["acento"],
                      button_hover_color=C["acento_h"], progress_color=C["acento"],
                      command=lambda _v: programar()).pack(side="left")
        ctk.CTkLabel(w, text="Si queda una sombra del papel, subí la intensidad; si se pierden trazos finos, bajala.",
                     font=F(11), text_color=C["texto2"], anchor="w").pack(fill="x", padx=20, pady=(6, 0))
        pie = ctk.CTkFrame(w, fg_color="transparent")
        pie.pack(fill="x", padx=20, pady=14)
        trabajo = {"id": None}

        def programar():
            if trabajo["id"]:
                w.after_cancel(trabajo["id"])
            trabajo["id"] = w.after(150, actualizar)

        def actualizar():
            trabajo["id"] = None
            est["res"] = quitar_fondo_imagen(original, v_quitar.get(), float(v_int.get()))
            if est["res"] is None:
                l_prev.configure(image=None, text="No quedó nada: bajá la intensidad.")
                return
            W_, H_ = 440, 220
            vista_ = Image.new("RGBA", (W_ * 2, H_ * 2), (255, 255, 255, 255))
            dch = ImageDraw.Draw(vista_)
            for yy in range(0, H_ * 2, 16):
                for xx in range(0, W_ * 2, 16):
                    if (xx // 16 + yy // 16) % 2:
                        dch.rectangle([xx, yy, xx + 15, yy + 15], fill=(232, 236, 241, 255))
            im_ = est["res"].copy()
            im_.thumbnail((W_ * 2 - 40, H_ * 2 - 40), Image.LANCZOS)
            vista_.alpha_composite(im_, ((W_ * 2 - im_.width) // 2, (H_ * 2 - im_.height) // 2))
            est["foto"] = ctk.CTkImage(vista_, size=(W_, H_))
            l_prev.configure(image=est["foto"], text="")

        def guardar_():
            if est["res"] is None:
                return
            nombre = f"{clave_cat()[:-1]}_{int(time.time() * 1000)}.png"
            try:
                est["res"].save(os.path.join(carpeta_firmas(), nombre), optimize=True)
            except Exception as e:
                messagebox.showerror(NOMBRE, f"No se pudo guardar:\n{e}")
                return
            k_ = clave_cat()
            almacen.datos[k_] = [nombre] + lista_firmas()
            almacen.datos[k_[:-1] + "_ult"] = nombre
            almacen.guardar()
            w.destroy()
            dibujar_firmas_panel()
            v_estado.set("Guardada. Hacé clic en la hoja donde va.")

        boton(pie, "Guardar", primario=True, ancho=110, command=guardar_).pack(side="right", padx=(8, 0))
        boton(pie, "Cancelar", ancho=96, command=w.destroy).pack(side="right")
        w.bind("<Escape>", lambda _e: w.destroy())
        actualizar()
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + (raiz.winfo_height() - w.winfo_reqheight()) // 3}")
        w.after(100, lambda: (w.grab_set(), w.focus_force()))

    # ---- texto
    def ayuda_texto():
        v_texto_ayuda.set("Hacé clic en la hoja y escribí ahí mismo; «✓ Listo» o clic afuera lo deja puesto. El "
                          "borde lo mueve y los tiradores cambian el tamaño (como una autoforma de Word). Clic adentro "
                          "para corregirlo; clic derecho o Supr lo quita." if v_tmodo.get() == "Agregar" else
                          ("Hacé clic sobre un texto del PDF para cambiarlo. Se toma el párrafo entero" if v_talc.get() == "Párrafo"
                           else "Hacé clic sobre un texto del PDF para cambiarlo. Se toma el renglón") +
                          " y se escribe con la misma fuente (o la más parecida). Después podés cambiarle la fuente, el "
                          "tamaño o el color desde aquí; también se puede mover. En escaneos, el texto se reconoce solo (OCR).")

    def estilo_panel():
        return {"fam": v_tfuente.get(), "neg": bool(v_tneg.get()), "cur": bool(v_tcur.get()),
                "sub": bool(v_tsub.get()), "tach": bool(v_ttach.get()), "alin": ALINEAS.get(v_talin.get(), "izq"),
                "interlin": INTERLINEADOS.get(v_tinter.get()), "fondo": bool(v_tfondo.get())}

    def sincronizar_panel(it_):
        """Al elegir un texto en la hoja, el panel muestra su fuente, tamaño y color."""
        texto_col["sincro"] = True
        try:
            v_tfuente.set(it_.get("fam", "Helvetica (PDF)"))
            v_tneg.set(bool(it_.get("neg")))
            v_tcur.set(bool(it_.get("cur")))
            v_tsub.set(bool(it_.get("sub")))
            v_ttach.set(bool(it_.get("tach")))
            v_tfondo.set(bool(it_.get("fondo")))
            v_talin.set({v__: k__ for k__, v__ in ALINEAS.items()}.get(it_.get("alin", "izq"), "Izq."))
            v_tinter.set({v__: k__ for k__, v__ in INTERLINEADOS.items()}.get(it_.get("interlin"), "Original"))
            v_ttam.set(("%g" % round(it_["tam"], 1)).replace(".", ","))
            color_texto(it_["color"], aplicar=False)
        finally:
            texto_col["sincro"] = False

    def tam_texto():
        try:
            return max(4.0, min(144.0, float(v_ttam.get().replace(",", "."))))
        except ValueError:
            return 12.0

    def color_texto(rgb, aplicar=True):
        texto_col["rgb"] = tuple(int(x) for x in rgb)
        for b_, c_ in texto_col["puntos"]:
            b_.configure(border_width=3 if tuple(c_) == texto_col["rgb"] else 0)
        if aplicar:
            estilo_texto_cambio()

    def estilo_texto_cambio():
        if texto_col.get("sincro"):
            return
        ed_i = vis.get("ined")
        if ed_i:  # v4.1: escribiendo en la hoja: el estilo cambia ahi mismo
            it_ = ed_i["it"]
            nuevo_ = dict(estilo_panel(), tam=tam_texto(), color=texto_col["rgb"])
            if not ed_i["nuevo"]:
                guardar_historia("estilo", it_["id"])
            it_.update(nuevo_)
            if it_["tipo"] == "reemplazo":
                ajustar_reemplazo(it_)
            else:
                almacen.datos.update(texto_fuente=v_tfuente.get(), texto_negrita=bool(v_tneg.get()),
                                     texto_cursiva=bool(v_tcur.get()), texto_tam=tam_texto(),
                                     texto_color=list(texto_col["rgb"]))
            if not ed_i["nuevo"]:
                tocar(it_)
            ined_colocar(ed_i["vista"])
            def _refoco():
                f_ = raiz.focus_get()
                if vis.get("ined") is ed_i and not (f_ is not None and f_.winfo_class() == "Entry"):
                    ed_i["txt"].focus_set()
            raiz.after(20, _refoco)
            return
        e_ = vis.get("edit_item")
        if e_ and e_[2]["tipo"] in ("texto_n", "reemplazo"):  # cambia el texto elegido
            it_ = e_[2]
            nuevo_ = dict(estilo_panel(), tam=tam_texto(), color=texto_col["rgb"])
            if all(it_.get(k__) == v__ for k__, v__ in nuevo_.items()):
                return
            guardar_historia("estilo", it_["id"])
            it_.update(nuevo_)
            if it_["tipo"] == "texto_n":
                it_["rect"] = rect_texto(it_["rect"][:2], it_["txt"], it_)
            else:
                ajustar_reemplazo(it_)
            tocar(it_)
            visor_pedir_dibujo()
            if it_["tipo"] == "reemplazo":
                return  # el estilo de un texto del PDF no cambia lo que se usa para escribir texto nuevo
        almacen.datos.update(texto_fuente=v_tfuente.get(), texto_negrita=bool(v_tneg.get()),
                             texto_cursiva=bool(v_tcur.get()), texto_tam=tam_texto(), texto_color=list(texto_col["rgb"]))
        if not e_:
            return
        visor_pedir_dibujo()

    def rect_texto(esq, txt, it_):
        tam = it_["tam"]
        if it_.get("ancho"):  # v4.1: recuadro de ancho fijo
            lineas = partir_renglones(txt, it_, it_["ancho"]) or [""]
            ancho = it_["ancho"]
        else:
            lineas = txt.split("\n") or [""]
            ancho = max(ancho_texto(l_, it_) for l_ in lineas)
        it_ = dict(it_, tipo="texto_n")
        y1 = esq[1] + tam * 0.95 + (len(lineas) - 1) * paso_renglon(it_) + tam * 0.4
        if it_.get("alto"):  # v4.1.1: recuadro mas alto que el texto (como una autoforma)
            y1 = max(y1, esq[1] + it_["alto"])
        return (esq[0], esq[1], esq[0] + ancho + tam * 0.6, y1)

    def caja_texto(it_):
        """v4.1: donde esta el texto ahora (un parrafo cambiado y movido ya no ocupa su lugar original)."""
        if it_.get("tipo") != "reemplazo":
            return tuple(it_["rect"])
        r_ = None
        for x_, base, _l, _p, w_ in diseno_texto(it_):
            q_ = fitz.Rect(x_, base - it_["tam"], x_ + max(w_, 2) + 1, base + it_["tam"] * 0.3)
            r_ = q_ if r_ is None else r_ | q_
        if r_ is None:
            return tuple(it_["rect"])
        if it_.get("ancho"):
            r_.x1 = max(r_.x1, it_["origen"][0] + it_["ancho"])
        if it_.get("alto"):
            r_.y1 = max(r_.y1, r_.y0 + it_["alto"])
        return tuple(r_)

    def ajustar_reemplazo(it_):
        """Renglones del texto nuevo y la caja que ocupa (crece si el texto nuevo es mas largo)."""
        it_["lineas"] = partir_renglones(it_["txt"], it_, it_.get("ancho"))
        r_ = fitz.Rect(it_["rect_orig"])
        for x_, base, _l, _p, w_ in diseno_texto(it_):
            r_ |= fitz.Rect(x_, base - it_["tam"], x_ + w_ + 1, base + it_["tam"] * 0.3)
        it_["rect"] = tuple(r_)

    def pedir_texto(titulo, inicial="", info=""):
        """Ventanita para escribir (varios renglones). Devuelve el texto o None."""
        w = ctk.CTkToplevel(raiz)
        w.title(f"{NOMBRE} · {titulo.lower()}")
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        ctk.CTkLabel(w, text=titulo, font=F(14, "bold"), text_color=C["texto"], anchor="w").pack(
            fill="x", padx=20, pady=(16, 6))
        if info:
            ctk.CTkLabel(w, text=info, font=F(11), text_color=C["texto2"], anchor="w").pack(fill="x", padx=20,
                                                                                            pady=(0, 6))
        largo = len(inicial) > 90 or inicial.count("\n") > 1
        caja_ = ctk.CTkTextbox(w, width=520 if largo else 420, height=190 if largo else 110, font=F(13),
                               fg_color=C["campo"], text_color=C["texto"], border_color=C["borde"], border_width=1,
                               corner_radius=8, wrap="word")
        caja_.pack(padx=20)
        caja_.insert("1.0", inicial)
        ctk.CTkLabel(w, text="Enter: nuevo renglón · Ctrl+Enter: listo", font=F(11), text_color=C["texto2"],
                     anchor="w").pack(fill="x", padx=20, pady=(4, 0))
        res = {"t": None}

        def ok_(*_):
            res["t"] = caja_.get("1.0", "end").rstrip("\n")
            w.destroy()
            return "break"

        pie = ctk.CTkFrame(w, fg_color="transparent")
        pie.pack(fill="x", padx=20, pady=14)
        boton(pie, "Listo", primario=True, ancho=100, command=ok_).pack(side="right", padx=(8, 0))
        boton(pie, "Cancelar", ancho=96, command=w.destroy).pack(side="right")
        w.bind("<Escape>", lambda _e: w.destroy())
        caja_.bind("<Control-Return>", ok_)
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + (raiz.winfo_height() - w.winfo_reqheight()) // 3}")
        w.after(80, lambda: (w.grab_set(), caja_.focus_set()))
        raiz.wait_window(w)
        t_ = res["t"]
        return t_ if t_ is not None and t_.strip() else None

    def texto_en(ruta, pag, p_, parrafo=True):
        """El parrafo (o el renglon) del PDF bajo el punto (coordenadas de la pagina como se ve)."""
        try:
            d_ = fitz.open(ruta)
            pg = d_[pag]
            m_ = pg.rotation_matrix
            pt_ = fitz.Point(p_)
            bloques_ = pg.get_text("dict")["blocks"]
            ocr_r = None
            if not any(sp["text"].strip() for bl in bloques_ for ln in bl.get("lines", []) for sp in ln["spans"]):
                ocr_r = ocr_de(ruta, pag)  # v4.1: escaneo: el texto reconocido
                if ocr_r:
                    bloques_ = ocr_r["bloques"]
            for bl in bloques_:
                lineas = [ln for ln in bl.get("lines", []) if "".join(sp["text"] for sp in ln["spans"]).strip()]
                if not lineas:
                    continue
                cajas = [fitz.Rect(ln["bbox"]) * m_ for ln in lineas]
                dentro = [k_ for k_, r_ in enumerate(cajas) if r_.contains(pt_)]
                if not dentro:
                    continue
                elegidas = list(range(len(lineas))) if parrafo else dentro[:1]
                lineas = [lineas[k_] for k_ in elegidas]
                cajas = [cajas[k_] for k_ in elegidas]
                d0 = fitz.Point(lineas[0]["dir"]) * m_ - fitz.Point(0, 0) * m_
                if abs(d0.y) > 0.01 or d0.x <= 0:
                    return "girado"
                spans = [sp for ln in lineas for sp in ln["spans"] if sp["text"].strip()]
                sp0 = max(spans, key=lambda sp: len(sp["text"].strip()))  # el estilo que mas se usa
                caja = fitz.Rect(cajas[0])
                for r_ in cajas[1:]:
                    caja |= r_
                textos = ["".join(sp["text"] for sp in ln["spans"]).strip() for ln in lineas]
                txt = ""
                for k_, t_ in enumerate(textos):  # se unen los renglones cortados por el ancho del parrafo
                    txt += t_
                    if k_ < len(textos) - 1:
                        lleno = cajas[k_].x1 >= caja.x0 + caja.width * 0.8 and not t_.endswith((".", ":", ";"))
                        txt += " " if lleno else "\n"
                bases = [(fitz.Point(ln["spans"][0]["origin"]) * m_) for ln in lineas]
                inter = ((bases[-1].y - bases[0].y) / (len(bases) - 1)) if len(bases) > 1 else sp0["size"] * 1.2
                n_ = sp0["font"]
                if ocr_r:  # v4.1: texto de un escaneo: se tapa con el color del papel y se escribe con el de la tinta
                    ln0 = lineas[0]
                    return {"rect": tuple(caja), "rects_borrar": [tuple(fitz.Rect(r_) + (-1.2, -1.2, 1.2, 1.2)) for r_ in cajas],
                            "txt": txt, "tam": round(sp0["size"], 2), "fam": "Arial" if "Arial" in fuentes_ed_disponibles()
                            else "Helvetica (PDF)", "neg": False, "cur": False, "color": tuple(ln0.get("tinta", (0, 0, 0))),
                            "fondo_borrar": tuple(ln0.get("papel", (255, 255, 255))), "ocr": True,
                            "origen": (min(b_.x for b_ in bases), bases[0].y), "inter": max(1.0, inter),
                            "ancho": caja.width + 1 if len(lineas) > 1 else None, "fuente_pdf": ""}
                return {"rect": tuple(caja), "rects_borrar": [tuple(r_) for r_ in cajas], "txt": txt,
                        "tam": round(sp0["size"], 2), "fam": familia_de(n_, sp0["flags"]),
                        "neg": bool(sp0["flags"] & 16) or any(w_ in n_.lower() for w_ in ("bold", "black", "heavy")),
                        "cur": bool(sp0["flags"] & 2) or "italic" in n_.lower() or "oblique" in n_.lower(),
                        "color": ((sp0["color"] >> 16) & 255, (sp0["color"] >> 8) & 255, sp0["color"] & 255),
                        "origen": (min(b_.x for b_ in bases), bases[0].y), "inter": max(1.0, inter),
                        "ancho": caja.width + 1 if len(lineas) > 1 else None, "fuente_pdf": n_}
        except Exception:
            pass
        return None

    # ---- en la hoja: poner, mover, cambiar tamaño
    def agregar_item(ruta, pag, item):
        vis["nres"] += 1
        guardar_historia()
        item.update(id=vis["nres"], ver=0, op=item.get("op", 1.0), color=tuple(item.get("color", (0, 0, 0))))
        tocar(item)
        vis["res"].setdefault(ruta, {}).setdefault(pag, []).append(item)
        vis["res_pila"].append((ruta, pag, item))
        vis["edit_item"] = (ruta, pag, item)
        if item["tipo"] in ("texto_n", "reemplazo"):
            sincronizar_panel(item)  # el panel muestra el estilo del texto elegido
        actualizar_resaltes()
        v_estado.set(f"{n_resaltes()} cambio(s) sin guardar · Ctrl+Z deshace · Ctrl+Y rehace · Ctrl+S guarda en el PDF.")

    # ================= v4.1: RECONOCER EL TEXTO DE PAGINAS ESCANEADAS (OCR)
    # La pagina en la que estas, si es un escaneo, se reconoce sola (en otro proceso): despues su texto se
    # selecciona, se copia y se cambia como cualquier texto del PDF
    ocr_q_ent, ocr_q_sal = mp.Queue(), mp.Queue()
    ocr_ = {"p": None, "pend": set(), "res": {}, "escaneo": {}, "visto": None}

    def es_escaneo(ruta, pag):
        k_ = (ruta, pag, ver_arch(ruta))
        if k_ not in ocr_["escaneo"]:
            r_ = False
            try:
                with fitz.open(ruta) as d_:
                    pg = d_[pag]
                    if not pg.get_text("text").strip():
                        area = abs(pg.rect)
                        cub = sum(abs(fitz.Rect(i_["bbox"]) & pg.rect) for i_ in pg.get_image_info())
                        r_ = area > 0 and cub >= area * 0.25
            except Exception:
                r_ = False
            if len(ocr_["escaneo"]) > 400:
                ocr_["escaneo"].clear()
            ocr_["escaneo"][k_] = r_
        return ocr_["escaneo"][k_]

    def ocr_de(ruta, pag):
        return ocr_["res"].get((ruta, pag, ver_arch(ruta)))

    def ocr_pedir(ruta, pag, avisar=True, forzar=False):
        """Pide reconocer la pagina si es un escaneo. True si se esta reconociendo (hay que esperar)."""
        k_ = (ruta, pag, ver_arch(ruta))
        if k_ in ocr_["res"]:
            return False
        if k_ in ocr_["pend"]:
            if avisar:
                v_estado.set(f"Reconociendo el texto de la página {pag + 1} (OCR)… un momento.")
            return True
        if not forzar and not es_escaneo(ruta, pag):
            return False
        if ocr_["p"] is None:
            try:
                ocr_["p"] = mp.Process(target=_proceso_ocr, args=(ocr_q_ent, ocr_q_sal), daemon=True)
                ocr_["p"].start()
                raiz.after(300, ocr_recibir)
            except Exception as e:
                ocr_["p"] = False
                v_estado.set(f"No se pudo reconocer el texto: {e}")
                return False
        if ocr_["p"] is False:
            return False
        ocr_["pend"].add(k_)
        ocr_q_ent.put(k_)
        v_estado.set(f"Reconociendo el texto de la página {pag + 1} (OCR)…" if avisar else
                     f"Página {pag + 1} escaneada: reconociendo su texto (OCR)…")
        return True

    def ocr_recibir():
        try:
            while True:
                ruta, pag, ver_, letras, bloques = ocr_q_sal.get_nowait()
                k_ = (ruta, pag, ver_)
                ocr_["pend"].discard(k_)
                if letras is None:
                    ocr_["res"][k_] = {"letras": [], "bloques": [], "error": bloques}
                    v_estado.set(f"No se pudo reconocer el texto de la página {pag + 1}: {bloques}")
                    continue
                ocr_["res"][k_] = {"letras": [tuple(c_) for c_ in letras], "bloques": bloques}
                vis["chars"][k_] = [tuple(c_) for c_ in letras]  # ya se puede seleccionar y copiar
                vis["chars"].pop(("pedido",) + k_, None)
                v_estado.set((f"Texto reconocido en la página {pag + 1}: ya podés seleccionarlo, copiarlo o "
                              "cambiarlo (panel Texto › Cambiar).") if letras else
                             f"En la página {pag + 1} no se encontró texto para reconocer.")
                visor_pedir_dibujo()
        except Exception:
            pass
        raiz.after(250, ocr_recibir)

    def copiar_texto_ocr(ruta, pag):
        oc_ = ocr_de(ruta, pag)
        if not oc_:
            return
        renglones, ult = [], None
        for c_ in oc_["letras"]:
            if c_[4] != ult:
                renglones.append("")
                ult = c_[4]
            renglones[-1] += c_[5]
        raiz.clipboard_clear()
        raiz.clipboard_append("\n".join(r_.rstrip() for r_ in renglones))
        v_estado.set(f"Texto de la página {pag + 1} copiado ({len(renglones)} renglones).")

    def ocr_pagina_actual():
        """Cada tanto: si la pagina a la vista es un escaneo y te quedaste en ella, se reconoce sola."""
        try:
            v_ = vista_activa()
            if app["pagina"] == "visor" and v_ and v_.lay and v_.lay["pags"] and not vis["comp"]:
                ruta, pag, _r = v_.lay["pags"][min(v_.pag, len(v_.lay["pags"]) - 1)]
                k_ = (ruta, pag, ver_arch(ruta))
                if ocr_["visto"] == k_:
                    if k_ not in ocr_["res"] and k_ not in ocr_["pend"]:
                        ocr_pedir(ruta, pag, avisar=False)
                ocr_["visto"] = k_
        except Exception:
            pass
        raiz.after(900, ocr_pagina_actual)
    raiz.after(3000, ocr_pagina_actual)

    # ================= v4.1: EDITAR TEXTO DIRECTO EN LA HOJA (como un cuadro de texto de Word)
    # El texto se escribe sobre la hoja, en su lugar, dentro de un recuadro con tiradores: arrastrando el borde
    # se mueve; los tiradores de los costados cambian el ancho (el texto se acomoda en renglones).
    NARANJA_W = "#F97316"
    _fams_tk = {}

    def familia_tk(fam):
        if not _fams_tk:
            try:
                _fams_tk.update({f_.lower(): f_ for f_ in tkfont.families(raiz)})
            except Exception:
                pass
        n_ = {"Helvetica (PDF)": "Arial", "Times (PDF)": "Times New Roman", "Courier (PDF)": "Courier New"}.get(fam, fam)
        for c_ in (n_, n_.split(" (")[0], "Arial", "Helvetica", "Liberation Sans", "DejaVu Sans"):
            if c_.lower() in _fams_tk:
                return _fams_tk[c_.lower()]
        return "Arial"

    def ined_activo():
        return vis.get("ined")

    def _ined_escala(ed):
        """Zoom (pixeles por punto) y matriz de la hoja en la vista; None si la hoja esta girada."""
        v_ = ed["vista"]
        if not v_.lay:
            return None
        for i_, (r_, p_, rot_) in enumerate(v_.lay["pags"]):
            if r_ == ed["ruta"] and p_ == ed["pag"]:
                z_ = v_.lay["zs"][i_]
                M = matriz_vista(v_.lay["dims"][i_][0], v_.lay["dims"][i_][1], z_, rot_, v_.lay["parar"])
                if abs(M.b) > 1e-6 or M.a <= 0:
                    return None
                return M, v_.lay["xs"][i_], v_.lay["ys"][i_], i_
        return None

    def _ined_fuente(ed, M):
        it_ = ed["it"]
        z_ = M.a
        clave = (it_.get("fam"), bool(it_.get("neg")), bool(it_.get("cur")), bool(it_.get("sub")),
                 bool(it_.get("tach")), round(it_["tam"] * z_, 1))
        if ed.get("fk") != clave:
            ed["fk"] = clave
            ed["font"] = tkfont.Font(root=raiz, family=familia_tk(it_.get("fam", "Helvetica (PDF)")),
                                     size=-max(4, round(it_["tam"] * z_)), weight="bold" if it_.get("neg") else "normal",
                                     slant="italic" if it_.get("cur") else "roman", underline=bool(it_.get("sub")),
                                     overstrike=bool(it_.get("tach")))
        return ed["font"]

    def _ined_origen(it_):
        """Esquina del primer renglon: (x, base) en coordenadas de la hoja."""
        if it_["tipo"] == "reemplazo":
            return it_["origen"]
        r_ = fitz.Rect(it_["rect"])
        return r_.x0 + it_["tam"] * 0.3, r_.y0 + it_["tam"] * 0.95

    def _ined_ancho_pt(ed):
        it_ = ed["it"]
        if it_.get("ancho"):
            return it_["ancho"]
        txt_ = ed["txt"].get("1.0", "end-1c") if ed.get("txt") else it_.get("txt", "")
        w_ = max([ancho_texto(l_, it_) for l_ in txt_.split("\n")] + [it_["tam"] * 2])
        if it_["tipo"] == "reemplazo":
            w_ = max(w_, fitz.Rect(it_["rect_orig"]).x1 - it_["origen"][0])
        return w_

    def caja_texto_ed(ed):
        it_ = ed["it"]
        if it_["tipo"] == "texto_n":
            return rect_texto(it_["rect"][:2], ed["txt"].get("1.0", "end-1c"), it_)
        return caja_texto(dict(it_, txt=ed["txt"].get("1.0", "end-1c")))

    def ined_colocar(vista):
        """Pone (o vuelve a poner) el cuadro de escritura y su recuadro en la vista (se llama al dibujar)."""
        ed = vis.get("ined")
        if not ed or ed["vista"] is not vista:
            return
        g_ = _ined_escala(ed)
        cv_ = vista.cv
        if not g_:
            ined_terminar(True)
            return
        M, x, y, _i = g_
        it_ = ed["it"]
        z_ = M.a
        fnt = _ined_fuente(ed, M)
        t_w = ed["txt"]
        c_txt = "#%02X%02X%02X" % tuple(int(v_) for v_ in it_["color"])
        fondo_ = "#%02X%02X%02X" % tuple(int(v_) for v_ in it_.get("fondo_borrar", (255, 255, 255)))
        alin_ = {"centro": "center", "der": "right"}.get(it_.get("alin"), "left")
        paso_px = paso_renglon(it_) * z_
        extra = max(0, round(paso_px - fnt.metrics("linespace")))
        t_w.configure(font=fnt, fg=c_txt, insertbackground=c_txt, bg=fondo_, spacing3=extra,
                      wrap="word" if it_.get("ancho") else "none")
        t_w.tag_configure("al", justify=alin_)
        t_w.tag_add("al", "1.0", "end")
        ox, base = _ined_origen(it_)
        p0 = fitz.Point(ox, base) * M
        W = max(px(24), round(_ined_ancho_pt(ed) * z_) + 4 + (0 if it_.get("ancho") else max(6, round(it_["tam"] * z_ * 0.6))))
        X = x + p0.x - 2
        Y = y + p0.y - fnt.metrics("ascent") - 2
        txt_ = t_w.get("1.0", "end-1c")
        n_lin = len(partir_renglones(txt_, it_, it_["ancho"])) if it_.get("ancho") else txt_.count("\n") + 1
        try:  # lo que Tk acomoda (por si corta distinto que el PDF)
            if it_.get("ancho") and t_w.winfo_ismapped():
                n_lin = max(n_lin, int(t_w.count("1.0", "end", "displaylines")[0]))
        except Exception:
            pass
        H = max(1, n_lin) * (fnt.metrics("linespace") + extra) + 4
        if it_.get("alto"):  # v4.1.1: recuadro mas alto que el texto
            H = max(H, round(it_["alto"] * z_))
        cv_.delete("ined")
        fsin = fondo_sin_texto(dict(it_, rect=it_["rect_orig"]), z_) if it_["tipo"] == "reemplazo" else None
        if fsin is not None:  # v4.3: la hoja real sin las letras (no un parche blanco)
            ed["foto_fondo"] = foto_tk(fsin)
            q0_ = fitz.Rect(it_["rect_orig"]) * M
            cv_.create_image(x + q0_.x0, y + q0_.y0, image=ed["foto_fondo"], anchor="nw", tags="ined")
            if "fondo_vivo" not in ed:
                ed["fondo_vivo"] = "#%02X%02X%02X" % color_dominante(fsin)
            fondo_ = ed["fondo_vivo"]
            t_w.configure(bg=fondo_)
        elif it_["tipo"] == "reemplazo":  # tapa el texto original mientras se escribe
            for rb_ in it_.get("rects_borrar") or [it_["rect_orig"]]:
                q_ = fitz.Rect(rb_) * M
                cv_.create_rectangle(x + q_.x0, y + q_.y0, x + q_.x1, y + q_.y1, fill=fondo_, outline="", tags="ined")
        cv_.create_window(X, Y, window=t_w, anchor="nw", width=W, height=H, tags="ined")
        ed["caja"] = (X, Y, X + W, Y + H)
        dibujar_marco_word(cv_, X - 3, Y - 3, X + W + 3, Y + H + 3, "ined")
        # v4.1.1: boton «Listo» debajo del recuadro (tambien: clic afuera o Ctrl+Enter)
        bw_, bh_ = px(64), px(24)
        bx_, by_ = X + W + 3 - bw_, Y + H + px(10)
        cv_.create_rectangle(bx_, by_, bx_ + bw_, by_ + bh_, fill=NARANJA_W, outline="", tags=("ined", "ined_listo"))
        cv_.create_text(bx_ + bw_ / 2, by_ + bh_ / 2, text="✓ Listo", fill="#FFFFFF", font=(FAM, 9, "bold"),
                        tags=("ined", "ined_listo"))
        ed["listo"] = (bx_, by_, bx_ + bw_, by_ + bh_)

    def dibujar_marco_word(cv_, x0, y0, x1, y1, tag):
        """Recuadro punteado con 8 tiradores (como Word)."""
        cv_.create_rectangle(x0, y0, x1, y1, outline=NARANJA_W, width=1, dash=(4, 3), tags=tag)
        t_ = px(4)
        xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
        for hx, hy in ((x0, y0), (xm, y0), (x1, y0), (x0, ym), (x1, ym), (x0, y1), (xm, y1), (x1, y1)):
            cv_.create_rectangle(hx - t_, hy - t_, hx + t_, hy + t_, fill="#FFFFFF", outline=NARANJA_W, width=1.5,
                                 tags=tag)

    def tirador_en(caja, cx_, cy_):
        """Que parte del recuadro esta bajo el puntero: un tirador ('n', 's', 'e', 'o', 'ne', 'no', 'se', 'so'),
        'borde' (mover), 'dentro' o None."""
        x0, y0, x1, y1 = caja[0] - 3, caja[1] - 3, caja[2] + 3, caja[3] + 3
        m_ = px(7)
        if not (x0 - m_ <= cx_ <= x1 + m_ and y0 - m_ <= cy_ <= y1 + m_):
            return None
        xm, ym = (x0 + x1) / 2, (y0 + y1) / 2
        v_ = "n" if abs(cy_ - y0) <= m_ else ("s" if abs(cy_ - y1) <= m_ else "")
        h_ = "o" if abs(cx_ - x0) <= m_ else ("e" if abs(cx_ - x1) <= m_ else "")
        if v_ and h_:
            return v_ + h_
        if h_ and abs(cy_ - ym) <= m_ + 2:
            return h_
        if v_ and abs(cx_ - xm) <= m_ + 2:
            return v_
        if v_ or h_:
            return "borde"
        return "dentro"

    CURSOR_TIRADOR = {"n": "sb_v_double_arrow", "s": "sb_v_double_arrow", "e": "sb_h_double_arrow",
                      "o": "sb_h_double_arrow", "ne": "size_ne_sw", "so": "size_ne_sw", "no": "size_nw_se",
                      "se": "size_nw_se", "borde": "fleur", "dentro": "xterm"}

    def cursor_tirador(cv_, t_):
        c_ = CURSOR_TIRADOR.get(t_, "")
        try:
            cv_.configure(cursor=c_ if c_ else cursor_herramienta())
        except tk.TclError:  # en Linux no estan las flechas en diagonal
            cv_.configure(cursor="fleur" if t_ else cursor_herramienta())

    def caja_item_vista(vista, it_, base):
        _i, ruta, pag, M, x, y = base
        r_ = fitz.Rect(caja_texto(it_)) * M
        return (x + r_.x0, y + r_.y0, x + r_.x1, y + r_.y1)

    def ined_empezar(vista, ruta, pag, it_, nuevo):
        """Abre el cuadro de escritura sobre el texto (nuevo o ya puesto)."""
        ined_terminar(True)
        ed = {"vista": vista, "ruta": ruta, "pag": pag, "it": it_, "nuevo": nuevo, "orig": it_.get("txt", "")}
        if not _ined_escala(ed):  # hoja girada: se usa la ventanita
            return False
        t_w = tk.Text(vista.cv, bd=0, highlightthickness=0, relief="flat", padx=0, pady=0, undo=True,
                      maxundo=-1, cursor="xterm", exportselection=True, selectbackground="#BFDBFE",
                      selectforeground="#0F172A")
        t_w.insert("1.0", it_.get("txt", ""))
        t_w.edit_reset()
        ed["txt"] = t_w
        vis["ined"] = ed
        vis["edit_item"] = None if nuevo else (ruta, pag, it_)
        sincronizar_panel(it_)

        def cambio(_e=None):
            raiz.after_idle(lambda: ined_colocar(vista) if vis.get("ined") is ed else None)

        def estilo_tecla(k_):
            {"b": v_tneg, "i": v_tcur, "u": v_tsub}[k_].set(not {"b": v_tneg, "i": v_tcur, "u": v_tsub}[k_].get())
            estilo_texto_cambio()
            return "break"
        t_w.bind("<KeyRelease>", cambio)
        t_w.bind("<<Paste>>", lambda e: raiz.after(10, cambio))
        t_w.bind("<Escape>", lambda e: (ined_terminar(False), "break")[1])
        t_w.bind("<Control-Return>", lambda e: (ined_terminar(True), "break")[1])
        for k_ in ("z", "Z"):
            t_w.bind(f"<Control-{k_}>", lambda e: (t_w.edit_undo() if t_w.edit("canundo") else None, cambio(), "break")[2])
        for k_ in ("y", "Y"):
            t_w.bind(f"<Control-{k_}>", lambda e: (t_w.edit_redo() if t_w.edit("canredo") else None, cambio(), "break")[2])
        for k_ in ("b", "i", "u"):
            t_w.bind(f"<Control-{k_}>", lambda e, k_=k_: estilo_tecla(k_))
            t_w.bind(f"<Control-{k_.upper()}>", lambda e, k_=k_: estilo_tecla(k_))
        t_w.bind("<Control-a>", lambda e: (t_w.tag_add("sel", "1.0", "end-1c"), "break")[1])
        t_w.bind("<Control-s>", lambda e: (ined_terminar(True), guardar_resaltados_dialogo(), "break")[2])
        t_w.bind("<Control-f>", lambda e: "break")
        t_w.bind("<MouseWheel>", lambda e: vista.cv.event_generate("<MouseWheel>", delta=e.delta, x=0, y=0))
        visor_pedir_dibujo()
        vista.dibujar()
        t_w.focus_set()
        t_w.mark_set("insert", "end-1c")
        v_estado.set("Escribí directo en la hoja · arrastrá el borde para moverlo · los tiradores de los costados "
                     "cambian el ancho · clic afuera o Ctrl+Enter: listo · Esc: cancelar.")
        return True

    def ined_terminar(guardar=True):
        ed = vis.pop("ined", None)
        if not ed:
            return
        t_w = ed["txt"]
        txt = t_w.get("1.0", "end-1c")
        try:
            ed["vista"].cv.delete("ined")
            t_w.destroy()
        except Exception:
            pass
        it_ = ed["it"]
        ruta, pag = ed["ruta"], ed["pag"]
        if not guardar:
            if ed["nuevo"]:
                vis["edit_item"] = None
            visor_pedir_dibujo()
            return
        if ed["nuevo"]:
            if it_["tipo"] == "texto_n":
                if txt.strip():
                    it_["txt"] = txt
                    it_["rect"] = rect_texto(it_["rect"][:2], txt, it_)
                    agregar_item(ruta, pag, it_)
            elif txt != ed["orig"] or ed.get("movido"):
                it_["txt"] = txt
                ajustar_reemplazo(it_)
                agregar_item(ruta, pag, it_)
            else:
                vis["edit_item"] = None
        elif txt != it_["txt"]:
            if not txt.strip() and it_["tipo"] == "texto_n":
                vis["edit_item"] = None
                quitar_resaltado(ruta, pag, it_)
                v_estado.set("Texto quitado · Ctrl+Z lo vuelve a poner.")
                return
            guardar_historia()
            it_["txt"] = txt
            if it_["tipo"] == "texto_n":
                it_["rect"] = rect_texto(it_["rect"][:2], txt, it_)
            else:
                ajustar_reemplazo(it_)
            tocar(it_)
        n_c = n_resaltes()
        v_estado.set(f"Texto listo · {n_c} cambio(s) sin guardar · «Guardar cambios» (Ctrl+S) lo deja en el PDF."
                     if n_c else "Listo.")
        visor_pedir_dibujo()
        mini_pedir_dibujo()

    def mover_texto(it_, dx, dy):
        """Mueve un texto (nuevo o un parrafo cambiado del PDF) dx, dy puntos."""
        if it_["tipo"] == "reemplazo":
            ox, oy = it_["origen"]
            it_["origen"] = (ox + dx, oy + dy)
            ajustar_reemplazo(it_)
        else:
            it_["rect"] = tuple(fitz.Rect(it_["rect"]) + (dx, dy, dx, dy))

    def alto_minimo(it_):
        n_ = max(1, len(partir_renglones(it_["txt"], it_, it_["ancho"])) if it_.get("ancho") else it_["txt"].count("\n") + 1)
        return it_["tam"] * 1.25 + (n_ - 1) * paso_renglon(it_)

    def redimensionar_texto(it_, t_, dx, dy, r0):
        """Como una autoforma de Word: los costados cambian el ancho, arriba y abajo el alto, las esquinas ambos."""
        if "e" in t_ or "o" in t_:
            ancho_texto_item(it_, "der" if "e" in t_ else "izq", dx, r0[:2])
        if "n" in t_ or "s" in t_:
            alto0 = r0[2]
            nuevo_ = max(alto_minimo(it_), alto0 + (dy if "s" in t_ else -dy))
            if "n" in t_:
                mover_texto(it_, 0, alto0 - nuevo_)
            it_["alto"] = nuevo_
            if it_["tipo"] == "texto_n":
                it_["rect"] = rect_texto(it_["rect"][:2], it_["txt"], it_)

    def ancho_texto_item(it_, lado, dx, r0):
        """Cambia el ancho del recuadro desde un costado (r0: ancho y origen al empezar)."""
        ancho0, ox0 = r0
        if lado == "der":
            nuevo_ = max(it_["tam"] * 2, ancho0 + dx)
        else:
            nuevo_ = max(it_["tam"] * 2, ancho0 - dx)
            mov_ = ancho0 - nuevo_
            if it_["tipo"] == "reemplazo":
                it_["origen"] = (ox0 + mov_, it_["origen"][1])
            else:
                r_ = fitz.Rect(it_["rect"])
                it_["rect"] = (ox0 + mov_ - it_["tam"] * 0.3, r_.y0, r_.x1, r_.y1)
        it_["ancho"] = nuevo_
        if it_["tipo"] == "reemplazo":
            ajustar_reemplazo(it_)
        else:
            it_["rect"] = rect_texto(it_["rect"][:2], it_["txt"], it_)

    def _foto_texto(it_):
        return (tuple(it_["rect"]), it_.get("origen"), it_.get("ancho"), it_.get("lineas"), it_.get("alto"))

    def _volver_foto(it_, f_):
        it_["rect"], org_, it_["ancho"], lin_, it_["alto"] = f_
        if org_ is not None:
            it_["origen"] = org_
        if lin_ is not None:
            it_["lineas"] = lin_
        if f_[2] is None:
            it_.pop("ancho", None)
        if f_[4] is None:
            it_.pop("alto", None)

    def edicion_press(vista, ev):
        cx_, cy_ = vista.cv.canvasx(ev.x), vista.cv.canvasy(ev.y)
        ed = vis.get("ined")
        recien_cerrado = False
        if ed and ed.get("listo") and ed["vista"] is vista:  # v4.1.1: boton «Listo»
            bx0, by0, bx1, by1 = ed["listo"]
            if bx0 <= cx_ <= bx1 and by0 <= cy_ <= by1:
                ined_terminar(True)
                vista._ed = {"modo": "nada"}
                return True
        if ed:  # v4.1: escribiendo en la hoja: el borde mueve, los tiradores cambian el tamaño, afuera termina
            g_ = _ined_escala(ed) if ed["vista"] is vista else None
            t_ = tirador_en(ed["caja"], cx_, cy_) if (g_ and ed.get("caja")) else None
            if t_ in ("n", "s", "e", "o", "ne", "no", "se", "so") or t_ == "borde":
                base_e = (g_[3], ed["ruta"], ed["pag"], g_[0], g_[1], g_[2])
                it_ = ed["it"]
                vista._ed = {"it": it_, "base": base_e, "p0": vista._pt(ev, base_e), "ined": True,
                             "modo": "mover" if t_ == "borde" else t_, "foto": _foto_texto(it_),
                             "r0": (_ined_ancho_pt(ed), _ined_origen(it_)[0],
                                    fitz.Rect(caja_texto_ed(ed)).height)}
                return True
            ined_terminar(True)
            recien_cerrado = True  # v4.1.1: el clic sigue (puede elegir otro texto), pero no crea uno nuevo
        base = vista._punto_pagina(cx_, cy_)
        if not base:
            if recien_cerrado:
                vista._ed = {"modo": "nada"}
            return recien_cerrado
        _i, ruta, pag, M, x, y = base
        p_ = vista._pt(ev, base)
        e_ = vis.get("edit_item")
        if e_ and e_[0] == ruta and e_[1] == pag and e_[2]["tipo"] == "firma":  # tirador de la esquina
            q_ = fitz.Point(e_[2]["rect"][2], e_[2]["rect"][3]) * M
            if abs(q_.x + x - cx_) < 11 and abs(q_.y + y - cy_) < 11:
                vista._ed = {"it": e_[2], "base": base, "p0": p_, "r0": tuple(e_[2]["rect"]), "modo": "tam"}
                return True
        if e_ and e_[0] == ruta and e_[1] == pag and e_[2]["tipo"] in ("texto_n", "reemplazo"):
            it_ = e_[2]  # v4.1: el texto elegido: costados = ancho, borde = mover, adentro = escribir
            t_ = tirador_en(caja_item_vista(vista, it_, base), cx_, cy_)
            if t_:
                ed0 = {"it": it_, "txt": None}
                vista._ed = {"it": it_, "base": base, "p0": p_, "foto": _foto_texto(it_),
                             "modo": t_ if t_ in ("n", "s", "e", "o", "ne", "no", "se", "so") else "mover", "editar": t_ == "dentro",
                             "r0": (_ined_ancho_pt(ed0), _ined_origen(it_)[0], fitz.Rect(caja_texto(it_)).height)}
                return True
        for it_ in reversed(vis["res"].get(ruta, {}).get(pag, [])):
            if it_["tipo"] in EDITABLES and fitz.Rect(caja_texto(it_)).contains(fitz.Point(p_)):
                vis["edit_item"] = (ruta, pag, it_)
                if it_["tipo"] in ("texto_n", "reemplazo"):
                    sincronizar_panel(it_)
                vista._ed = {"it": it_, "base": base, "p0": p_, "r0": tuple(it_["rect"]), "foto": _foto_texto(it_),
                             "modo": "mover"}
                visor_pedir_dibujo()
                return True
        if vis.get("edit_item"):  # clic fuera: se suelta la que estaba elegida
            soltada = vis["edit_item"][2]["tipo"] in ("texto_n", "reemplazo")
            vis["edit_item"] = None
            visor_pedir_dibujo()
            if soltada and app.get("panel") == "texto" and v_tmodo.get() == "Agregar":
                return True  # v4.1.1: como en Word, el clic afuera solo suelta el recuadro (no crea otro)
        if recien_cerrado and app.get("panel") == "texto" and v_tmodo.get() == "Agregar":
            vista._ed = {"modo": "nada"}
            return True
        if app.get("panel") == "firmar":
            nombre = firma_elegida()
            if not nombre:
                v_estado.set("Primero agregá una firma o un sello (panel de la derecha).")
                return True
            try:
                with Image.open(os.path.join(carpeta_firmas(), nombre)) as im_:
                    prop = im_.height / max(1, im_.width)
            except Exception:
                return True
            dims = vista.lay["dims"][_i]
            ancho = min(dims[0], dims[1]) * (0.30 if clave_cat() == "firmas" else 0.22)
            alto = ancho * prop
            r_ = (p_[0] - ancho / 2, p_[1] - alto / 2, p_[0] + ancho / 2, p_[1] + alto / 2)
            almacen.datos[clave_cat()[:-1] + "_ult"] = nombre
            agregar_item(ruta, pag, {"tipo": "firma", "rect": r_, "archivo": os.path.join(carpeta_firmas(), nombre)})
            return True
        if app.get("panel") == "texto":
            if v_tmodo.get() == "Agregar":
                it_ = dict(estilo_panel(), tipo="texto_n", txt="", tam=tam_texto(), color=texto_col["rgb"])
                it_["rect"] = rect_texto((p_[0], p_[1] - it_["tam"] * 0.6), "", it_)
                if ined_empezar(vista, ruta, pag, it_, True):  # v4.1: se escribe directo en la hoja
                    return True
                txt = pedir_texto("Escribí el texto")
                if txt:
                    it_["txt"] = txt
                    it_["rect"] = rect_texto((p_[0], p_[1] - it_["tam"] * 0.6), txt, it_)
                    agregar_item(ruta, pag, it_)
                return True
            sp_ = texto_en(ruta, pag, p_, v_talc.get() == "Párrafo")
            if sp_ is None and ocr_pedir(ruta, pag):  # v4.1: escaneo: primero se reconoce el texto
                return True
            if sp_ == "girado":
                v_estado.set("Ese texto está inclinado o vertical: por ahora solo se cambia texto horizontal.")
                return True
            if not sp_:
                v_estado.set("Ahí no hay texto del PDF para cambiar.")
                return True
            it_n = dict(sp_, tipo="reemplazo", txt=sp_["txt"], orig=sp_["txt"], rect_orig=sp_["rect"], ruta=ruta, pag=pag)
            ajustar_reemplazo(it_n)
            if ined_empezar(vista, ruta, pag, it_n, True):  # v4.1: se corrige directo en la hoja
                return True
            txt = pedir_texto("Cambiar el párrafo" if sp_["ancho"] else "Cambiar el texto", sp_["txt"],
                              f"Fuente: {sp_['fam']} {('%g' % sp_['tam']).replace('.', ',')} pt"
                              + (f"  (en el PDF: {sp_['fuente_pdf'].split('+')[-1]})" if sp_["fuente_pdf"] else ""))
            if txt is not None and txt != sp_["txt"]:
                it_ = dict(sp_, tipo="reemplazo", txt=txt, orig=sp_["txt"], rect_orig=sp_["rect"], ruta=ruta, pag=pag)
                ajustar_reemplazo(it_)
                agregar_item(ruta, pag, it_)
            return True
        return False

    def edicion_motion(vista, ev):
        ed = vista._ed
        if ed["modo"] == "nada":
            return
        p_ = vista._pt(ev, ed["base"])
        dx, dy = p_[0] - ed["p0"][0], p_[1] - ed["p0"][1]
        if abs(dx) + abs(dy) > 1.5:
            ed["movio"] = True
        if ed.get("foto") and ed["it"]["tipo"] in ("texto_n", "reemplazo"):  # v4.1: mover o cambiar el ancho
            if not ed.get("movio"):
                return
            it_ = ed["it"]
            pendiente = ed.get("ined") and vis.get("ined", {}).get("nuevo")
            if not ed.get("hist") and not pendiente:
                ed["hist"] = True
                guardar_historia()
            _volver_foto(it_, ed["foto"])
            if ed["modo"] == "mover":
                mover_texto(it_, dx, dy)
            else:
                redimensionar_texto(it_, ed["modo"], dx, dy, ed["r0"])
            if ed.get("ined"):
                vis["ined"]["movido"] = True
                ined_colocar(vista)
                return
            tocar(it_)
            vista.dibujar()
            return
        x0, y0, x1, y1 = ed["r0"]
        if ed["modo"] == "tam":  # misma proporcion
            ancho = max(8.0, (x1 - x0) + dx)
            ed["it"]["rect"] = (x0, y0, x0 + ancho, y0 + ancho * (y1 - y0) / max(0.01, x1 - x0))
        else:
            ed["it"]["rect"] = (x0 + dx, y0 + dy, x1 + dx, y1 + dy)
        if not ed.get("hist"):
            ed["hist"] = True
            guardar_historia()
        tocar(ed["it"])
        vista.dibujar()

    def edicion_release(vista, ev):
        ed = vista._ed
        vista._ed = None
        if ed and ed.get("editar") and not ed.get("movio"):  # v4.1: clic adentro del texto elegido: a escribir
            e_ = vis.get("edit_item")
            if e_ and e_[2] is ed["it"]:
                ined_empezar(vista, e_[0], e_[1], e_[2], False)
                return
        mini_pedir_dibujo()

    def edicion_doble(vista, ev):
        e_ = vis.get("edit_item")
        if not e_ or e_[2]["tipo"] not in ("texto_n", "reemplazo"):
            return False
        it_ = e_[2]
        if ined_empezar(vista, e_[0], e_[1], it_, False):  # v4.1: directo en la hoja
            return True
        txt = pedir_texto("Editar el texto", it_["txt"])
        if txt and txt != it_["txt"]:
            guardar_historia()
            it_["txt"] = txt
            if it_["tipo"] == "texto_n":
                it_["rect"] = rect_texto(it_["rect"][:2], it_["txt"], it_)
            else:
                ajustar_reemplazo(it_)
            tocar(it_)
            visor_pedir_dibujo()
        return True

    def quitar_editado(*_):
        e_ = vis.get("edit_item")
        if not e_ or app["pagina"] != "visor":
            return
        foco = raiz.focus_get()
        if foco is not None and foco.winfo_class() in ("Entry", "Text"):
            return
        vis["edit_item"] = None
        quitar_resaltado(*e_)
        return "break"

    # ---- v4.3: como Acrobat/Nitro: al cambiar un texto se SACAN sus letras del PDF y queda lo que hay debajo
    # (color de fondo, celdas, sombreados). En pantalla se muestra la hoja real sin esas letras
    cache_fondo = {}

    def _rects_quitar(item):
        out = []
        for rb_ in item.get("rects_borrar") or [item["rect_orig"]]:
            r_ = fitz.Rect(rb_)
            corto = r_.height * 0.18  # solo el renglon (no los de arriba y abajo)
            out.append(fitz.Rect(r_.x0, r_.y0 + corto, r_.x1, r_.y1 - corto))
        return out

    def quitar_letras(pg, item):
        """Saca del PDF las letras del texto original (sin pintar nada: el fondo queda como estaba)."""
        dm = pg.derotation_matrix
        for r_ in _rects_quitar(item):
            pg.add_redact_annot(r_ * dm, fill=False)

    def fondo_sin_texto(item, z):
        """Imagen (RGB) de la zona del texto, con la hoja tal cual pero sin las letras originales."""
        ruta, pag = item.get("ruta"), item.get("pag")
        if ruta is None or pag is None or item.get("ocr"):
            return None
        r_ = fitz.Rect(item["rect"])
        k_ = (ruta, pag, ver_arch(ruta), tuple(tuple(round(v_, 2) for v_ in q_) for q_ in _rects_quitar(item)),
              tuple(round(v_, 2) for v_ in r_), round(z, 4))
        if k_ in cache_fondo:
            return cache_fondo[k_]
        img = None
        try:
            with fitz.open(ruta) as d_:
                d2 = fitz.open()
                d2.insert_pdf(d_, from_page=pag, to_page=pag)
                p2 = d2[0]
                quitar_letras(p2, item)
                p2.apply_redactions(images=fitz.PDF_REDACT_IMAGE_NONE, graphics=fitz.PDF_REDACT_LINE_ART_NONE,
                                    text=fitz.PDF_REDACT_TEXT_REMOVE)
                pix = p2.get_pixmap(matrix=fitz.Matrix(z, z), clip=r_, alpha=False, annots=False)
                img = Image.frombytes("RGB", (pix.width, pix.height), pix.samples)
                d2.close()
        except Exception:
            img = None
        if len(cache_fondo) > 40:
            cache_fondo.clear()
        cache_fondo[k_] = img
        return img

    def color_dominante(img):
        """El color que mas hay (el fondo de la zona): para el cuadro mientras se escribe."""
        try:
            chico = img.convert("RGB").resize((max(1, img.width // 6), max(1, img.height // 6)))
            cols_ = chico.getcolors(chico.width * chico.height) or []
            return max(cols_)[1] if cols_ else (255, 255, 255)
        except Exception:
            return (255, 255, 255)

    def imagen_edicion(item, M):
        """Firma, sello o texto como imagen en pantalla (y su esquina relativa a la pagina)."""
        r_ = fitz.Rect(item["rect"])
        qs = [p_ * M for p_ in (r_.tl, r_.tr, r_.br, r_.bl)]
        bx, by = min(q.x for q in qs), min(q.y for q in qs)
        z = math.hypot(M.a, M.b)
        ang = round(math.degrees(math.atan2(M.b, M.a)) / 90) % 4 * 90
        w_, h_ = max(1, round(r_.width * z)), max(1, round(r_.height * z))
        if item["tipo"] == "firma":
            k_ = ("img", item["archivo"])
            if k_ not in cache_firma:
                try:
                    cache_firma[k_] = Image.open(item["archivo"]).convert("RGBA")
                except Exception:
                    cache_firma[k_] = Image.new("RGBA", (10, 10), (0, 0, 0, 0))
            img = cache_firma[k_].resize((w_, h_), Image.LANCZOS)
        else:
            d_ = fitz.open()
            pg = d_.new_page(width=max(1.0, r_.width), height=max(1.0, r_.height))
            c_ = tuple(v_ / 255 for v_ in item["color"])
            fondo_ = fondo_sin_texto(item, z) if item["tipo"] == "reemplazo" else None
            if item["tipo"] == "reemplazo" and fondo_ is None:  # escaneo (o sin datos): color del papel
                fb_ = tuple(v_ / 255 for v_ in item.get("fondo_borrar", (255, 255, 255)))
                for rb_ in item.get("rects_borrar") or [item["rect_orig"]]:  # tapa el texto original en la vista
                    pg.draw_rect(fitz.Rect(rb_) - (r_.x0, r_.y0, r_.x0, r_.y0), color=None, fill=fb_)
            elif item.get("fondo") and item["tipo"] != "reemplazo":
                pg.draw_rect(pg.rect, color=None, fill=(1, 1, 1))
            dibujar_texto(pg, item, lambda q_: fitz.Point(q_) - r_.tl)
            pix = pg.get_pixmap(matrix=fitz.Matrix(z, z), alpha=True)
            img = Image.frombytes("RGBa", (pix.width, pix.height), pix.samples).convert("RGBA")  # MuPDF da alfa premultiplicado
            d_.close()
            if fondo_ is not None:  # v4.3: debajo, la hoja real sin las letras originales
                img = Image.alpha_composite(fondo_.resize(img.size).convert("RGBA"), img)
        if ang:
            img = img.rotate(-ang, expand=True)
        return int(bx), int(by), img

    def guardar_editables(pg, items_):
        """Escribe en la pagina las firmas, sellos y textos (quedan fijos en el PDF)."""
        dm = pg.derotation_matrix
        reemplazos = [it_ for it_ in items_ if it_["tipo"] == "reemplazo" and not it_.get("ocr")]
        for it_ in [x_ for x_ in items_ if x_["tipo"] == "reemplazo" and x_.get("ocr")]:  # v4.1: escaneo
            fb_ = tuple(v_ / 255 for v_ in it_.get("fondo_borrar", (255, 255, 255)))
            for rb_ in it_.get("rects_borrar") or [it_["rect_orig"]]:
                pg.draw_rect(fitz.Rect(rb_) * dm, color=None, fill=fb_, overlay=True)
            dibujar_texto(pg, it_, lambda q_: fitz.Point(q_) * dm, pg.rotation)
        if reemplazos:  # se borra el texto original (sin tocar dibujos ni imagenes) y se escribe el nuevo
            for it_ in reemplazos:  # v4.3: sin relleno (antes quedaba un rectangulo blanco)
                quitar_letras(pg, it_)
            pg.apply_redactions(images=fitz.PDF_REDACT_IMAGE_NONE, graphics=fitz.PDF_REDACT_LINE_ART_NONE,
                                text=fitz.PDF_REDACT_TEXT_REMOVE)
            for it_ in reemplazos:
                dibujar_texto(pg, it_, lambda q_: fitz.Point(q_) * dm, pg.rotation)
        for it_ in items_:
            if it_["tipo"] == "firma":
                pg.insert_image(fitz.Rect(it_["rect"]) * dm, filename=it_["archivo"], rotate=pg.rotation,
                                overlay=True)
            elif it_["tipo"] == "texto_n":
                if it_.get("fondo"):
                    pg.draw_rect(fitz.Rect(it_["rect"]) * dm, color=None, fill=(1, 1, 1), overlay=True)
                dibujar_texto(pg, it_, lambda q_: fitz.Point(q_) * dm, pg.rotation)

    def preguntar_resaltes(rutas, que):
        """Antes de cerrar / procesar: ofrece guardar los resaltados pendientes. False = cancelar."""
        n = n_resaltes(rutas)
        if not n:
            return True
        r_ = messagebox.askyesnocancel(NOMBRE, f"Hay {n} cambio(s) sin guardar (resaltados, firmas o textos).\n\n¿Guardarlos en el PDF antes "
                                               f"de {que}?\n(No = se descartan)")
        if r_ is None:
            return False
        if r_:
            guardar_resaltados(False, rutas)
        else:
            for x in list(rutas if rutas is not None else vis["res"]):
                vis["res"].pop(x, None)
            vis["res_pila"] = [x for x in vis["res_pila"] if x[0] in vis["res"]]
            limpiar_historia()
            actualizar_resaltes()
        return True

    # ================= lo que llega de los procesos
    def recibir_dibujos():
        hubo_p = hubo_m = hubo_b = False
        try:
            for _ in range(16):
                msg = q_sal.get_nowait()
                if msg[0] == "listo":
                    if not vis.get("render_listo"):
                        vis["render_listo"] = True
                        _tiempo("procesos de dibujo listos")
                        soltar_ayuda()
                    continue
                if msg[0] == "medidas":
                    _, ruta, med, err = msg
                    vis["med"][ruta] = med
                    if err:
                        v_estado.set(f"No se pudo abrir {os.path.basename(ruta)}: {err}")
                    hubo_p = hubo_m = True
                    continue
                if msg[0] == "hallazgos":
                    _, ident, lote, fin, hechas, total = msg
                    b_ = vis["busq"]
                    if b_ and b_["id"] == ident:
                        for pos, rects in lote:
                            b_["por_pos"][pos] = [tuple(r_) for r_ in rects]
                            b_["hits"].extend((pos, tuple(r_)) for r_ in rects)
                        b_["fin"], b_["hechas"], b_["total"] = fin, hechas, total
                        if b_["i"] < 0 and b_["hits"]:
                            busq_mover(1)
                        hubo_b = True
                    continue
                if msg[0] == "caracteres":
                    _, ruta, pag, ver_, chars = msg
                    if not chars and (ruta, pag, ver_) in ocr_["res"]:  # v4.1: ya se reconocio (OCR)
                        chars = ocr_["res"][(ruta, pag, ver_)]["letras"]
                    vis["chars"][(ruta, pag, ver_)] = [tuple(c_) for c_ in chars]
                    vis["chars"].pop(("pedido", ruta, pag, ver_), None)
                    if len(vis["chars"]) > 80:
                        for k_ in list(vis["chars"])[:30]:
                            vis["chars"].pop(k_, None)
                    continue
                k_, w_, h_, datos = msg
                if datos is None:
                    continue
                img = Image.frombytes("RGB", (w_, h_), datos)
                if k_[0] == "t":
                    vis["cache"][k_] = ImageTk.PhotoImage(img)
                    vis["lru"].append(k_)
                    hubo_p = True
                elif k_[1] == "imp":  # vista previa de Imprimir
                    vis.setdefault("imp_pil", {})[k_] = img
                    if len(vis["imp_pil"]) > 6:
                        vis["imp_pil"].pop(next(iter(vis["imp_pil"])))
                else:
                    vis["mcache"][k_] = ImageTk.PhotoImage(img)
                    vis["mlru"].append(k_)
                    hubo_m = True
        except queue.Empty:
            pass
        except Exception:
            pass
        if hubo_p:
            vis["ult"] = None
            visor_pedir_dibujo()
        if hubo_m:
            vis["ult_mini"] = None
            mini_pedir_dibujo()
        if hubo_b:
            busq_mostrar()
            visor_pedir_dibujo()
            mini_pedir_dibujo()
        raiz.after(30, recibir_dibujos)

    # ================= pestanas
    ORG_CLAVES = ("fuentes", "orden", "sel", "ancla", "pila", "rehacer", "ruta", "original", "origen")
    APP_CLAVES = ("scores", "umbral", "ruta", "salida", "n_paginas", "listas")
    cont_pest = {"n": 0}

    def guardar_estado(t_):
        t_["app"] = {k_: app.get(k_) for k_ in APP_CLAVES}
        t_["info"] = (v_info_doc.get(), v_info_apl.get(), v_detalle.get(), barra.get(), v_estado.get())
        t_["org"] = {k_: org.get(k_) for k_ in ORG_CLAVES}
        t_["orgver"] = vis["orgver"]
        t_["org_y"] = cv.yview()[0]
        for v_ in vistas:
            if v_.t is t_:
                v_.recordar()

    def org_reiniciar_cache():
        org["gen"] += 1
        org["pend"].clear()
        org["cache"].clear()
        org["lru"].clear()
        org["fotos"].clear()
        org["arrastre"] = None

    def estado_vacio():
        app["cargando"] = True
        try:
            V["ruta"].set("")
        finally:
            app["cargando"] = False
        app.update(scores=None, umbral=None, ruta=None, salida=None, n_paginas=None, listas=set())
        org.update(fuentes=[], orden=[], sel=set(), ancla=None, pila=[], rehacer=[], ruta=None, original=[], origen={})
        org_reiniciar_cache()
        vis["orgver"] += 1
        v_info_doc.set("Ningún documento seleccionado.")
        v_info_apl.set("Presioná «Analizar» para detectar los planos pesados.")
        v_detalle.set("")
        barra.set(0)

    def cargar_estado(t_):
        app["cargando"] = True
        try:
            V["ruta"].set(t_["ruta"])
        finally:
            app["cargando"] = False
        for k_, v_ in t_["app"].items():
            app[k_] = v_
        di, da, dd, bb, ee = t_["info"]
        v_estado.set(ee)
        v_info_doc.set(di)
        v_info_apl.set(da)
        v_detalle.set(dd)
        barra.set(bb)
        for k_ in ORG_CLAVES:
            org[k_] = t_["org"].get(k_, org.get(k_))
        org["sel"] = set(org.get("sel") or set())
        org_reiniciar_cache()
        vis["orgver"] = max(vis["orgver"], t_.get("orgver", 0)) + 1

    def ocupado_msg():
        if app["ocupado"] or org["preparando"]:
            v_estado.set("Esperá a que termine el proceso (o cancelalo) para cambiar de documento.")
            return True
        return False

    def activar_pestana(i, mostrar_visor=True):
        if vis.get("ined"):  # v4.1: lo que se estaba escribiendo en la hoja queda puesto
            ined_terminar(True)
        if app.get("vista_top") and mostrar_visor:  # v3.2: tocar un documento deja Inicio / Herramientas
            app["vista_top"] = None
            raiz.after_idle(lambda: (mostrar_inicio(), dibujar_superior()))
        if i == vis["act"]:
            if mostrar_visor and app["pagina"] != "visor":
                mostrar_pagina("visor")
            return
        if ocupado_msg():
            return
        t_ant = pest_activa()
        if t_ant:
            guardar_estado(t_ant)
        vis["act"] = i
        t_ = pest[i]
        cargar_estado(t_)
        vis["seleccion"] = None
        texto_busq = None
        if vis["busq"] and vis["busq"]["tab"] != t_["id"]:
            texto_busq = vis["busq"]["texto"]
            busq_cerrar()
        # que vista muestra la pestana
        if vis["comp"]:
            if vistas[0].t is t_ or vistas[1].t is t_:
                pass
            else:
                lado = 0 if vistas[0].t is t_ant else 1
                vistas[lado].poner(t_)
        else:
            vistas[0].poner(t_)
        for v_ in vistas:
            v_.poner(v_.t)
        vis["ult"] = vis["ult_mini"] = None
        dibujar_pestanas()
        refrescar()
        refrescar_boton_guardar()
        actualizar_ejemplo()
        if mostrar_visor and app["pagina"] != "visor":
            mostrar_pagina("visor")
        elif app["pagina"] == "organizar":
            org_entrar()
            raiz.after(60, lambda: cv.yview_moveto(t_.get("org_y", 0)))
        cvm.yview_moveto(0)
        raiz.after(30, lambda: (visor_dibujar(), mini_ver(t_.get("pag", 0)), mini_dibujar()))
        if texto_busq and vis["comp"]:  # comparando: la misma busqueda en el lado que se eligio
            raiz.after(80, lambda: buscar_texto(texto_busq))

    def abrir_pestana(r_, mostrar_visor=True):
        """Abre el PDF en una pestana nueva (o va a la suya si ya esta abierto)."""
        r_ = os.path.normpath(os.path.abspath(r_))
        for i, t_ in enumerate(pest):
            if os.path.normcase(t_["ruta"]) == os.path.normcase(r_):
                activar_pestana(i, mostrar_visor)
                return True
        if ocupado_msg():
            return False
        if not os.path.isfile(r_):
            messagebox.showerror(NOMBRE, f"No encuentro el archivo:\n{r_}")
            return False
        try:
            contar_paginas(r_)
        except Exception as e:
            messagebox.showerror(NOMBRE, f"No se pudo abrir:\n{r_}\n\n{e}")
            return False
        t_ant = pest_activa()
        if t_ant:
            guardar_estado(t_ant)
        if mostrar_visor and app.get("vista_top"):  # v4.0.1: abierto desde Inicio (recientes): se ve enseguida
            app["vista_top"] = None
            raiz.after_idle(lambda: (mostrar_inicio(), dibujar_superior()))
        cont_pest["n"] += 1
        t_ = {"id": cont_pest["n"], "ruta": r_, "nombre": os.path.basename(r_), "pag": 0, "frac": 0.0,
              "org_y": 0, "zoom": almacen.datos.get("zoom_inicial", "Ajustar ancho"),
              "modo_vista": "continua", "giro": 0}
        recordar_reciente(r_)
        pest.append(t_)
        vis["act"] = len(pest) - 1
        if vis["busq"]:
            busq_cerrar()
        estado_vacio()
        _abrir_documento(r_)  # lo de la v1.1: ruta, paginas, MB, paginas ya listas
        org["ruta"] = r_
        org_cargar([r_])     # el orden de las paginas (lo usan miniaturas, copiar/pegar y Organizar)
        t_["app"] = {k_: app.get(k_) for k_ in APP_CLAVES}
        medidas_listas(t_)
        if vis["comp"]:
            lado = 0 if vistas[0].t is t_ant else 1
            vistas[lado].poner(t_)
        else:
            vistas[0].poner(t_)
        vis["ult"] = vis["ult_mini"] = None
        dibujar_pestanas()
        if mostrar_visor and app["pagina"] != "visor":
            mostrar_pagina("visor")
        cvm.yview_moveto(0)
        visor_dibujar()
        mini_dibujar()
        raiz.after(250, redibujar_todo)  # v2.5: que nunca quede la hoja del documento anterior
        return True

    def tiene_organizado(t_):
        o_ = org_de(t_)
        orden_ = o_.get("orden") or []
        return bool(orden_) and (len(o_.get("fuentes") or []) > 1 or orden_ != o_.get("original")
                                 or bool(o_.get("origen")))

    # ================= guardar cambios al cerrar (nunca se pierde informacion sin preguntar)
    def rutas_de(t_):
        return set(org_de(t_).get("fuentes") or []) | {t_["ruta"]}

    def tiene_cambios(t_):
        return tiene_organizado(t_) or n_resaltes(rutas_de(t_)) > 0

    def dialogo_guardar_cambios(t_):
        """Guardar / No guardar / Cancelar. Devuelve 'guardar', 'no' o 'cancelar'."""
        if os.environ.get("PDFOL_PRUEBA_RESPUESTA"):  # solo pruebas automaticas
            return os.environ["PDFOL_PRUEBA_RESPUESTA"]
        res = {"v": "cancelar"}
        o_ = org_de(t_)
        w = ctk.CTkToplevel(raiz)
        w.title(f"{NOMBRE} · guardar cambios")
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        ctk.CTkLabel(w, text=f"¿Guardar los cambios de «{t_['nombre']}»?", font=F(15, "bold"), text_color=C["texto"],
                     anchor="w").pack(fill="x", padx=24, pady=(20, 8))
        lineas = []
        n_r = n_resaltes(rutas_de(t_))
        if n_r:
            lineas.append(f"•  {n_r} resaltado(s) nuevo(s)")
        if tiene_organizado(t_):
            n_p, n_f = len(o_.get("orden") or []), len(o_.get("fuentes") or [])
            lineas.append(f"•  Páginas organizadas: {n_p} páginas" + (f" de {n_f} PDF" if n_f > 1 else ""))
        ctk.CTkLabel(w, text="\n".join(lineas), font=F(12), text_color=C["texto"], anchor="w", justify="left").pack(
            fill="x", padx=26)
        expl = []
        if n_r:
            expl.append("Los resaltados se agregan al mismo PDF.")
        if tiene_organizado(t_):
            base_ = (o_.get("origen") or {}).get(o_["fuentes"][0], o_["fuentes"][0])
            expl.append(f"Las páginas organizadas se guardan como «{os.path.basename(nombre_salida(base_))}» "
                        "(el original no se toca).")
        ctk.CTkLabel(w, text=" ".join(expl), font=F(11), text_color=C["texto2"], anchor="w", justify="left",
                     wraplength=440).pack(fill="x", padx=24, pady=(10, 0))
        pie = ctk.CTkFrame(w, fg_color="transparent")
        pie.pack(fill="x", padx=24, pady=18)

        def fin(v_):
            res["v"] = v_
            w.destroy()
        boton(pie, "Guardar", primario=True, ancho=110, command=lambda: fin("guardar")).pack(side="right", padx=(8, 0))
        boton(pie, "No guardar", ancho=120, command=lambda: fin("no")).pack(side="right", padx=(8, 0))
        boton(pie, "Cancelar", ancho=100, command=lambda: fin("cancelar")).pack(side="right")
        w.bind("<Escape>", lambda _e: fin("cancelar"))
        w.bind("<Return>", lambda _e: fin("guardar"))
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + (raiz.winfo_height() - w.winfo_reqheight()) // 3}")
        w.after(80, lambda: (_tenir_barra_titulo(w, modo_oscuro()), w.focus_force()))
        try:
            w.grab_set()
        except Exception:
            pass
        raiz.wait_window(w)
        return res["v"]

    def guardar_cambios(t_):
        """Guarda resaltados (en el mismo PDF) y paginas organizadas (PDF nuevo _PdFOL). True si salio bien."""
        rutas_t = rutas_de(t_)
        if n_resaltes(rutas_t):
            guardar_resaltados(False, rutas_t)
            if n_resaltes(rutas_t):  # quedo algo sin guardar (hubo error)
                return False
        if tiene_organizado(t_):
            o_ = org_de(t_)
            fuentes_ = list(o_["fuentes"])
            base_ = (o_.get("origen") or {}).get(fuentes_[0], fuentes_[0])
            dest = nombre_salida(base_)
            v_estado.set(f"Guardando {os.path.basename(dest)}…")
            pr = mp.Process(target=armar_organizado, args=(list(o_["orden"]), fuentes_, dest), daemon=True)
            pr.start()
            while pr.is_alive():  # la ventana sigue respondiendo mientras se arma
                raiz.update()
                time.sleep(0.05)
            if pr.exitcode != 0 or not os.path.isfile(dest):
                messagebox.showerror(NOMBRE, f"No se pudo guardar:\n{dest}\n\nNo se cerró nada.")
                return False
            v_estado.set(f"Guardado: {os.path.basename(dest)}")
            v_detalle.set(dest)
            app["salida"] = dest
        return True

    def descartar_resaltes(rutas_t):
        for x in rutas_t:
            vis["res"].pop(x, None)
        vis["res_pila"] = [x for x in vis["res_pila"] if x[0] in vis["res"]]
        limpiar_historia()
        actualizar_resaltes()

    def confirmar_cierre(t_):
        """Pregunta si hay cambios. False = no cerrar."""
        if not tiene_cambios(t_):
            return True
        r_ = dialogo_guardar_cambios(t_)
        if r_ == "cancelar":
            return False
        if r_ == "guardar":
            return guardar_cambios(t_)
        descartar_resaltes(rutas_de(t_))
        return True

    def cerrar_pestana(i, preguntar=True):
        if vis.get("ined"):  # v4.1: lo que se estaba escribiendo en la hoja queda puesto
            ined_terminar(True)
        if i is None or not 0 <= i < len(pest):
            return
        t_ = pest[i]
        if i == vis["act"] and ocupado_msg():
            return
        if preguntar and not confirmar_cierre(t_):
            return
        rutas_t = rutas_de(t_)
        if vis["comp"] and (vistas[0].t is t_ or vistas[1].t is t_):
            separar(quedar=vistas[1] if vistas[0].t is t_ else vistas[0])
        era_activa = i == vis["act"]
        if not era_activa and pest_activa():
            guardar_estado(pest_activa())
        pest.pop(i)
        if vis["busq"] and vis["busq"]["tab"] == t_["id"]:
            busq_cerrar()
        en_uso = {r_ for t2 in pest for r_ in (set(org_de(t2).get("fuentes") or []) | {t2["ruta"]})}
        for r_ in rutas_t - en_uso:
            soltar_archivo(r_)
            vis["med"].pop(r_, None)
            vis["pedida"].discard(r_)
        for v_ in vistas:
            if v_.t is t_:
                v_.poner(None)
        if era_activa:
            vis["act"] = None
            estado_vacio()
            if pest:
                activar_pestana(min(i, len(pest) - 1), mostrar_visor=False)
        else:
            vis["act"] = vis["act"] - 1 if vis["act"] > i else vis["act"]
        dibujar_pestanas()
        refrescar()
        actualizar_ejemplo()
        if app["pagina"] == "organizar":
            org_entrar()
        visor_dibujar()
        mini_dibujar()

    def dibujar_pestanas():
        columna_izquierda()
        for w_ in caja_pest.winfo_children():
            w_.destroy()
        vis["pest_w"] = {}
        if not pest:
            ctk.CTkLabel(caja_pest, text="Sin documentos abiertos", font=F(12), text_color=C["texto2"]).pack(
                side="left", padx=8, pady=4)
            return
        ancho_disp = max(150, superior.winfo_width() - X_PEST - 320)
        max_txt = max(3, min(34, int((ancho_disp / max(1, len(pest)) - 56) / 7.5)))
        en_comp = {id(v_.t) for v_ in vistas[:2]} if vis["comp"] else set()
        for i, t_ in enumerate(pest):
            activa = i == vis["act"]
            f_ = ctk.CTkFrame(caja_pest, fg_color=C["tarjeta"] if (activa or id(t_) in en_comp) else C["suave"],
                              corner_radius=8, border_width=1 if not activa else 2,
                              border_color=C["acento"] if activa else C["borde"], height=32)
            f_.pack(side="left", padx=(0, 6))
            nom = t_["nombre"] if len(t_["nombre"]) <= max_txt else t_["nombre"][:max_txt - 1] + "…"
            if tiene_organizado(t_):
                nom = "● " + nom  # tiene paginas organizadas sin procesar
            l_ = ctk.CTkLabel(f_, text=nom, font=F(12, "bold" if activa else "normal"),
                              text_color=C["texto"] if activa else C["texto2"], cursor="hand2")
            l_.pack(side="left", padx=(12, 4), pady=3)
            x_ = ctk.CTkButton(f_, text="✕", width=22, height=22, corner_radius=11, font=F(11),
                               fg_color="transparent", hover_color=C["suave_h"], text_color=C["texto2"],
                               command=lambda i_=i: cerrar_pestana(i_))
            x_.pack(side="left", padx=(0, 6))
            for w_ in (f_, l_):
                vis["pest_w"][str(w_)] = i
                w_.bind("<ButtonPress-1>", lambda e, i_=i: vis.update(arr_pest=(i_, e.x_root, e.y_root)))
                w_.bind("<ButtonRelease-1>", soltar_pestana)
                w_.bind("<Button-2>", lambda e, i_=i: cerrar_pestana(i_))  # clic con la rueda cierra
            for w_ in (l_._label, getattr(f_, "_canvas", None)):
                if w_ is not None:
                    vis["pest_w"][str(w_)] = i
            l_.bind("<Enter>", lambda e, tip_=t_["ruta"]: v_detalle.set(tip_) if not app["ocupado"] else None)

    pest_tarea = {"id": None, "ancho": 0}

    def _barra_vis_cambio(ev):
        # la barra del visor crece (busqueda, comparar): las pestanas se achican para que entren
        if abs(ev.width - pest_tarea["ancho"]) < 4:
            return
        pest_tarea["ancho"] = ev.width
        if pest_tarea["id"]:
            raiz.after_cancel(pest_tarea["id"])
        pest_tarea["id"] = raiz.after(60, dibujar_pestanas)

    superior.bind("<Configure>", _barra_vis_cambio, add="+")  # v3.0: las pestanas viven arriba

    def soltar_pestana(ev):
        a_ = vis.get("arr_pest")
        vis["arr_pest"] = None
        if not a_:
            return
        i, x0_, y0_ = a_
        j = widget_pestana(raiz.winfo_containing(ev.x_root, ev.y_root))
        if j is not None and j != i and abs(ev.x_root - x0_) + abs(ev.y_root - y0_) > 10:
            comparar(i, j)  # pestana arrastrada sobre otra: lado a lado
        elif j == i or j is None:
            activar_pestana(i)

    def abrir_archivos(*_):
        rs = filedialog.askopenfilenames(title="Abrir PDF", filetypes=[("PDF", "*.pdf")])
        for r_ in rs or ():
            if not abrir_pestana(r_):
                break

    # ================= comparar
    def comparar(i, j):
        if not (0 <= i < len(pest) and 0 <= j < len(pest)) or i == j:
            return
        if app["pagina"] != "visor":
            mostrar_pagina("visor")
        vis["comp"] = app["comparando"] = True
        vistas[0].poner(pest[i])
        vistas[1].poner(pest[j])
        area_doc.grid_columnconfigure(1, weight=1, uniform="vistas")
        vistas[0].marco.grid(row=0, column=0, sticky="nsew", padx=(0, 4))
        vistas[1].marco.grid(row=0, column=1, sticky="nsew", padx=(4, 0))
        chk_juntas.pack(side="right", padx=(10, 0))
        b_separar.pack(side="right", padx=(10, 0))
        if vis["act"] != i:
            activar_pestana(i, mostrar_visor=False)
        for v_ in vistas:
            v_.poner(v_.t)
            if v_.t is not None and v_.t.get("modo_vista") != "mosaico":  # v3.6: empieza en miniaturas
                v_.t["vista_previa"] = (v_.t.get("modo_vista", "continua"), v_.zoom)
                v_.t["modo_vista"] = "mosaico"
                v_.zoom = "Miniaturas"
                v_.v_zoom.set("Miniaturas")
                v_._zoom_mini = None
                v_.lay = v_.lay_k = None
                v_._pendiente_pos = (0, 0.0)
        if "juntas_previo" not in vis:  # cada PDF se recorre por su cuenta (para pasar hojas de uno a otro)
            vis["juntas_previo"] = v_juntas.get()
            v_juntas.set(False)
        dibujar_pestanas()
        dibujar_lateral()
        v_estado.set("Comparando en miniaturas: arrastrá una hoja al otro PDF (copia; con Shift la mueve) · "
                     "Ctrl+rueda o − / + las agranda · doble clic ve una hoja grande.")
        raiz.after(40, visor_dibujar)

    def separar(quedar=None):
        if not vis["comp"]:
            return
        quedar = quedar or vista_activa()
        t_q = quedar.t
        vis["comp"] = app["comparando"] = False
        for v_ in vistas:  # v3.6: cada PDF vuelve a como se veia antes de comparar
            t_v = v_.t
            if t_v is not None and t_v.get("vista_previa"):
                t_v["modo_vista"], z_v = t_v.pop("vista_previa")
                t_v["zoom"] = z_v if z_v != "Miniaturas" else "Ajustar ancho"
                if v_ is quedar:
                    v_.zoom = t_v["zoom"]
                    v_.v_zoom.set(f"{v_.zoom:g} %" if isinstance(v_.zoom, float) else v_.zoom)
            v_._zoom_mini = None
        if "juntas_previo" in vis:
            v_juntas.set(vis.pop("juntas_previo"))
        vistas[1].marco.grid_forget()
        area_doc.grid_columnconfigure(1, weight=0, uniform="")
        vistas[0].marco.grid(row=0, column=0, sticky="nsew", padx=0)
        chk_juntas.pack_forget()
        b_separar.pack_forget()
        vistas[0].poner(None)
        vistas[1].poner(None)
        vistas[0].poner(t_q)
        if t_q is not None and t_q in pest and pest.index(t_q) != vis["act"]:
            activar_pestana(pest.index(t_q), mostrar_visor=False)
        dibujar_pestanas()
        dibujar_lateral()
        raiz.after(40, visor_dibujar)

    def boton_comparar():
        if vis["comp"]:
            separar()
            return
        if len(pest) < 2:
            v_estado.set("Para comparar abrí otro PDF (o arrastrá una pestaña sobre otra).")
            return
        if len(pest) == 2:
            comparar(vis["act"], 1 - vis["act"])
            return
        m_ = menu_contextual()
        for k_, t_ in enumerate(pest):
            if k_ != vis["act"]:
                m_.add_command(label=f"Comparar con «{t_['nombre']}»", command=lambda k__=k_: comparar(vis["act"], k__))
        m_.tk_popup(superior.winfo_rootx() + 600, superior.winfo_rooty() + px(36) - 6)

    # ================= panel de herramienta (Aplanar / Foliar / Comprimir) a la derecha
    iconos_panel = {c_: ctk.CTkImage(_icono(c_, col_, 26 * 3), size=(26, 26)) for c_, _t, col_, *_r in ICONOS}

    def abrir_panel(clave):
        if vis.get("ined"):  # v4.1: lo que se estaba escribiendo en la hoja queda puesto
            ined_terminar(True)
        asegurar_pagina(clave)
        # Foliar, Aplanar y Comprimir tambien se abren al lado de Organizar; lo demas, en el visor
        if app["pagina"] != "visor" and not (app["pagina"] == "organizar" and clave in EN_PANEL):
            mostrar_pagina("visor")
        for k_, p_ in paneles.items():
            if k_ != clave and p_._parent_frame.winfo_manager():
                p_.pack_forget()
        v_panel_tit.set(TITULOS[clave])
        l_panel_ico.configure(image=iconos_panel[clave])
        if paneles[clave]._parent_frame.winfo_manager() != "pack":
            paneles[clave].pack(fill="both", expand=True, padx=2, pady=(4, 6))
        if not panel_der.winfo_ismapped():
            panel_der.grid(row=0, column=3, sticky="ns", padx=(0, 10), pady=(10, 12))
        app["panel"] = clave
        vis["edit_item"] = None
        columna_izquierda()
        for v_ in vistas:
            v_.cv.configure(cursor=cursor_herramienta())
        if clave == "firmar":
            v_estado.set("Firmar: elegí la firma o el sello y hacé clic en la hoja donde va.")
        elif clave == "texto":
            v_estado.set("Texto: hacé clic en la hoja para escribir, o elegí «Cambiar» y tocá un texto del PDF.")
        dibujar_lateral()
        if clave == "foliar":
            actualizar_ejemplo()
        raiz.after(30, visor_pedir_dibujo)

    def cerrar_panel():
        if vis.get("ined"):  # v4.1: lo que se estaba escribiendo en la hoja queda puesto
            ined_terminar(True)
        panel_der.grid_forget()
        app["panel"] = None
        vis["edit_item"] = None
        columna_izquierda()
        for v_ in vistas:
            v_.cv.configure(cursor=cursor_herramienta())
        dibujar_lateral()
        raiz.after(30, visor_pedir_dibujo)

    # ================= imprimir (ventana propia con el estilo de PdFOL)
    imp = {"devmode": {}, "proc": None, "cancelar": None, "cola": None, "foto": None, "w": None}

    def abrir_imprimir(*_):
        t_ = pest_activa()
        if not t_:
            v_estado.set("Abrí un PDF para imprimir.")
            return
        if not medidas_listas(t_):
            v_estado.set("Esperá a que termine de abrir el documento.")
            return
        if imp["proc"] is not None:
            v_estado.set("Ya se está imprimiendo un documento.")
            return
        if imp["w"] is not None and imp["w"].winfo_exists():
            imp["w"].focus_force()
            return
        pags = paginas_de(t_)
        n = len(pags)
        v_act = vista_activa()
        actual = v_act.pag if v_act.t is t_ else t_.get("pag", 0)
        sel = sorted(org["sel"]) if org.get("orden") else []
        nombres, pred = impresoras_windows()
        w = ctk.CTkToplevel(raiz)
        imp["w"] = w
        w.title(f"{NOMBRE} · imprimir")
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        cab = ctk.CTkFrame(w, fg_color="transparent")
        cab.pack(fill="x", padx=22, pady=(16, 6))
        ctk.CTkLabel(cab, text="", image=iconos_panel["imprimir"]).pack(side="left", padx=(0, 10))
        ctk.CTkLabel(cab, text="Imprimir", font=F(20, "bold"), text_color=C["texto"]).pack(side="left")
        ctk.CTkLabel(cab, text=t_["nombre"], font=F(12), text_color=C["texto2"]).pack(side="left", padx=12)
        cuerpo = ctk.CTkFrame(w, fg_color="transparent")
        cuerpo.pack(fill="both", padx=22)
        izq = ctk.CTkFrame(cuerpo, fg_color="transparent")
        izq.pack(side="left", fill="y")
        der = ctk.CTkFrame(cuerpo, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
        der.pack(side="left", fill="y", padx=(14, 0))

        def tarjeta(master):
            f_ = ctk.CTkFrame(master, fg_color=C["tarjeta"], corner_radius=12, border_width=1, border_color=C["borde"])
            f_.pack(fill="x", pady=(0, 8))
            f_.grid_columnconfigure(1, weight=1)
            return f_

        def fila(f_, r, texto, widget):
            ctk.CTkLabel(f_, text=texto, font=F(13), text_color=C["texto"], anchor="w").grid(
                row=r, column=0, sticky="w", padx=(16, 10), pady=8)
            widget.grid(row=r, column=1, sticky="e", padx=(10, 14), pady=8)

        # impresora
        t1 = tarjeta(izq)
        v_imp = tk.StringVar(value=pred or (nombres[0] if nombres else "(no hay impresoras)"))
        caja_i = ctk.CTkFrame(t1, fg_color="transparent")
        menu(caja_i, nombres or ["(no hay impresoras)"], v_imp, ancho=250).pack(side="left")
        b_prop = boton(caja_i, "Propiedades", ancho=104)
        b_prop.configure(height=30, font=F(12))
        b_prop.pack(side="left", padx=(6, 0))
        fila(t1, 0, "Impresora", caja_i)
        # paginas
        t2 = tarjeta(izq)
        v_cuales = tk.StringVar(value="Todas")
        v_rango = tk.StringVar(value="")
        caja_p = ctk.CTkFrame(t2, fg_color="transparent")
        opciones = [("Todas", f"Todas ({n})"), ("Actual", f"La actual ({actual + 1})"),
                    ("Seleccionadas", f"Las seleccionadas ({len(sel)})"), ("Rango", "Rango:")]
        for k_, (val, txt) in enumerate(opciones):
            rb = ctk.CTkRadioButton(caja_p, text=txt, variable=v_cuales, value=val, font=F(12), text_color=C["texto"],
                                    fg_color=C["acento"], hover_color=C["acento_h"], command=lambda: actualizar())
            rb.grid(row=k_ // 2, column=(k_ % 2) * 2, sticky="w", padx=(0, 8), pady=3)
            if val == "Seleccionadas" and not sel:
                rb.configure(state="disabled")
        e_r = entrada(caja_p, v_rango, 110, placeholder_text="1-5, 8")
        e_r.grid(row=1, column=3, sticky="w")
        e_r.bind("<FocusIn>", lambda _e: v_cuales.set("Rango"))
        fila(t2, 0, "Páginas", caja_p)
        v_copias = tk.StringVar(value="1")
        v_inter = tk.BooleanVar(value=True)
        caja_c = ctk.CTkFrame(t2, fg_color="transparent")
        Contador(caja_c, v_copias, 1, 999, ancho=50).pack(side="left")
        ctk.CTkCheckBox(caja_c, text="Intercalar", variable=v_inter, font=F(12), text_color=C["texto"],
                        fg_color=C["acento"], hover_color=C["acento_h"], border_color=C["texto2"], checkbox_width=18,
                        checkbox_height=18, border_width=2).pack(side="left", padx=(12, 0))
        fila(t2, 1, "Copias", caja_c)
        # papel y tamano
        t3 = tarjeta(izq)
        v_papel = tk.StringVar(value="Automático")
        fila(t3, 0, "Papel", segmentado(t3, ["Automático", "Carta", "Oficio", "A3"], v_papel, ancho=300,
                                        cmd=lambda _v: actualizar()))
        ctk.CTkLabel(t3, text="Automático: carta, y A3 para los planos.", font=F(11), text_color=C["texto2"],
                     anchor="w").grid(row=1, column=0, columnspan=2, sticky="w", padx=16, pady=(0, 6))
        v_ajuste = tk.StringVar(value="Ajustar a la hoja")
        fila(t3, 2, "Tamaño", segmentado(t3, ["Ajustar a la hoja", "Tamaño real"], v_ajuste, ancho=260))
        ctk.CTkLabel(t3, text="Orientación automática: las hojas horizontales se paran con el encabezado hacia "
                              "la perforación (izquierda).", font=F(11), text_color=C["texto2"], anchor="w",
                     justify="left", wraplength=420).grid(row=3, column=0, columnspan=2, sticky="w", padx=16,
                                                          pady=(0, 6))
        v_folio = tk.BooleanVar(value=bool(V["fol"].get()))
        sw_f = switch(t3, v_folio)
        fila(t3, 4, "Con folio", sw_f)
        # vista previa chica
        ctk.CTkLabel(der, text="Vista previa", font=F(14, "bold"), text_color=C["texto"]).pack(anchor="w", padx=16,
                                                                                               pady=(14, 6))
        l_prev = ctk.CTkLabel(der, text="", width=230, height=300, fg_color=C["campo"], corner_radius=8)
        l_prev.pack(padx=16)
        v_cuenta = tk.StringVar(value="")
        ctk.CTkLabel(der, textvariable=v_cuenta, font=F(12), text_color=C["texto"], justify="left",
                     wraplength=230).pack(anchor="w", padx=16, pady=(10, 14))
        pie = ctk.CTkFrame(w, fg_color="transparent")
        pie.pack(fill="x", padx=22, pady=16)
        b_ok = boton(pie, "Imprimir", primario=True, ancho=120)
        b_ok.pack(side="right", padx=(8, 0))
        boton(pie, "Cancelar", ancho=100, command=w.destroy).pack(side="right")

        def indices():
            c_ = v_cuales.get()
            if c_ == "Actual":
                return [actual]
            if c_ == "Seleccionadas":
                return list(sel)
            if c_ == "Rango":
                try:
                    return sorted(parsear_paginas(v_rango.get(), n))
                except ValueError:
                    return []
            return list(range(n))

        def actualizar(*_):
            ids = indices()
            try:
                copias = max(1, int(v_copias.get()))
            except ValueError:
                copias = 1
            cuenta = {}
            for i in ids:
                ruta, pag, rot = pags[i]
                w0, h0 = dims_vista(vis["med"][ruta][pag], rot, False)
                pp = papel_de_pagina(w0, h0, v_papel.get())
                cuenta[pp] = cuenta.get(pp, 0) + copias
            if not ids:
                v_cuenta.set("No hay páginas para imprimir: revisá el rango.")
            else:
                v_cuenta.set(f"{len(ids)} página(s) × {copias} copia(s)\n" +
                             "  ·  ".join(f"{c_} hojas {pp.lower() if pp != 'A3' else 'A3'}" for pp, c_ in cuenta.items()))
            b_ok.configure(state="normal" if (ids and nombres or (ids and os.name != "nt")) else "disabled")
            # vista previa: la primera pagina tal como sale (parada y con folio)
            if ids:
                i = ids[0]
                ruta, pag, rot = pags[i]
                vw, vh = dims_vista(vis["med"][ruta][pag], rot, True)
                z = min(220 / max(vw, 1), 290 / max(vh, 1))
                f_f, firma = folio_de_posicion(n)
                fol_ = f_f(i) if v_folio.get() else None
                if fol_ is None and v_folio.get() and not V["fol"].get():
                    pass
                k_ = ("m", "imp", ruta, pag, rot, round(z, 4), firma if fol_ else None, fol_[1] if fol_ else None,
                      ver_arch(ruta))
                imp["clave"] = k_
                vis["imp_ped"] = [(k_, ruta, pag, z, rot, True, fol_, None)]
                vis["ult_mini"] = None
                q_min.put(("ver", (vis["ult_mini"] or []) + vis["imp_ped"]))
                mirar_prev()

        def mirar_prev():
            if not w.winfo_exists():
                return
            pil_ = vis.get("imp_pil", {}).get(imp.get("clave"))
            if pil_ is not None:
                l_prev.configure(image=ctk.CTkImage(pil_, size=pil_.size), width=pil_.width, height=pil_.height)
                vis["imp_ped"] = []
            else:
                w.after(150, mirar_prev)

        def propiedades():
            if os.name != "nt" or not nombres:
                return
            try:
                hwnd = ctypes_hwnd(w)
                imp["devmode"][v_imp.get()] = _devmode(v_imp.get(), imp["devmode"].get(v_imp.get()), hwnd,
                                                       preguntar=True)
            except Exception as e:
                messagebox.showerror(NOMBRE, f"No se pudieron abrir las propiedades de la impresora:\n{e}", parent=w)

        def imprimir_ya():
            ids = indices()
            if not ids:
                return
            try:
                copias = max(1, min(999, int(v_copias.get())))
            except ValueError:
                copias = 1
            f_f, _firma = folio_de_posicion(n)
            cfg_ = None
            if v_folio.get() and not V["fol"].get():  # folio pedido aca aunque Foliar este apagado
                try:
                    cfg_ = cfg_folio()
                    ind_ = rango_folio(cfg_, n)
                    pos_ = {p_: k_ for k_, p_ in enumerate(ind_)}
                    tot_ = int(cfg_["inicio"]) + len(ind_) - 1
                    f_f = lambda i: (cfg_, texto_folio(cfg_, int(cfg_["inicio"]) + pos_[i], tot_)) if i in pos_ else None
                except Exception:
                    f_f = lambda i: None
            lista = [(pags[i][0], pags[i][1], pags[i][2], f_f(i) if v_folio.get() else None) for i in ids]
            params = {"impresora": v_imp.get(), "devmode": imp["devmode"].get(v_imp.get()), "paginas": lista,
                      "copias": copias, "intercalar": bool(v_inter.get()), "papel": v_papel.get(),
                      "ajustar": v_ajuste.get() == "Ajustar a la hoja", "titulo": f"PdFOL · {t_['nombre']}",
                      "como_pdf": os.environ.get("PDFOL_IMPRIMIR_PDF")}
            w.destroy()
            imp["cancelar"], imp["cola"] = mp.Event(), mp.Queue()
            pr = mp.Process(target=_proceso_imprimir, args=(params, imp["cola"], imp["cancelar"]), daemon=True)
            pr.start()
            imp["proc"] = pr
            b_cancelar.configure(state="normal")
            v_estado.set(f"Imprimiendo «{t_['nombre']}» en {params['impresora']}…")
            barra.set(0)
            raiz.after(200, mirar_impresion)

        for v_ in (v_copias, v_folio, v_rango, v_cuales):
            v_.trace_add("write", actualizar)
        b_prop.configure(command=propiedades, state="normal" if (os.name == "nt" and nombres) else "disabled")
        b_ok.configure(command=imprimir_ya)
        w.bind("<Escape>", lambda _e: w.destroy())
        w.bind("<Return>", lambda _e: imprimir_ya())
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + max(0, (raiz.winfo_height() - w.winfo_reqheight()) // 3)}")
        w.after(80, lambda: (_tenir_barra_titulo(w, modo_oscuro()), w.focus_force()))
        actualizar()

    # ================= actualizaciones dentro de la app
    act = {"info": None, "nuevo": None, "tmp": None, "bajando": False, "cancelar": threading.Event()}

    def franja_mostrar(texto, botones):
        v_franja.set(texto)
        for w_ in caja_franja.winfo_children():
            w_.destroy()
        for txt, cmd, prim in botones:
            b_ = boton(caja_franja, txt, primario=prim, ancho=max(90, 8 * len(txt) + 30), command=cmd)
            b_.configure(height=30, font=F(12, "bold" if prim else "normal"))
            b_.pack(side="left", padx=4)
        franja.grid(row=1, column=0, sticky="ew")

    def franja_ocultar():
        franja.grid_forget()

    def buscar_actualizacion(manual=False):
        if manual:
            v_estado.set("Buscando actualizaciones…")

        def hilo():
            try:
                eventos.put(("version", ultima_version(), manual))
            except Exception as e:
                eventos.put(("version_error", str(e), manual))
        threading.Thread(target=hilo, daemon=True).start()

    def ver_cambios():
        """Lo que trae la version nueva, dentro de PdFOL (se lee de las notas del release)."""
        info = act["info"] or {}
        puntos = []
        for ln in (info.get("notas") or "").splitlines():
            ln = ln.strip().replace("**", "").replace("`", "")
            if ln.startswith(("- ", "* ")):
                puntos.append(ln[2:].strip())
            elif puntos and ln and not ln.startswith("#") and not ln.lower().startswith("descargas"):
                puntos[-1] += " " + ln
        ventana_novedades(f"Novedades de {info.get('tag', 'la versión nueva')}",
                          [(info.get("tag", ""), puntos or ["(Esta versión no trae notas.)"])],
                          botones=[("Actualizar ahora", lambda: (empezar_actualizacion()), True)])

    def ofrecer_version(info):
        act["info"] = info
        app["hay_nueva"] = True
        dibujar_lateral()
        franja_mostrar(f"Hay una versión nueva de PdFOL ({info['tag']}).",
                       [("Ver cambios", ver_cambios, False), ("Actualizar", empezar_actualizacion, True),
                        ("Más tarde", franja_ocultar, False)])

    def empezar_actualizacion():
        if not getattr(sys, "frozen", False):
            messagebox.showinfo(NOMBRE, "La actualización automática funciona en el programa portable (PdFOL.exe).\n\n"
                                        "Estás usando el .py: bajá la versión nueva desde «Ver cambios».")
            return
        app_dir = os.path.dirname(sys.executable)
        if not carpeta_escribible(app_dir):
            messagebox.showerror(NOMBRE, f"No se puede escribir en la carpeta del programa:\n{app_dir}\n\n"
                                         "Copiá la carpeta de PdFOL a un lugar tuyo (Documentos, Escritorio o una USB) "
                                         "y actualizá desde ahí.")
            return
        import tempfile
        act["tmp"] = tempfile.mkdtemp(prefix="PdFOL_actualizacion_")
        act["bajando"] = True
        act["cancelar"].clear()
        franja_mostrar(f"Descargando PdFOL {act['info']['tag']}…", [("Cancelar", lambda: act["cancelar"].set(), False)])
        info = act["info"]

        def hilo():
            try:
                nuevo = descargar_actualizacion(info, act["tmp"], lambda h, t_: eventos.put(("act_prog", h, t_)),
                                                act["cancelar"])
                eventos.put(("act_listo", nuevo))
            except Cancelado:
                eventos.put(("act_error", None))
            except Exception as e:
                eventos.put(("act_error", str(e)))
        threading.Thread(target=hilo, daemon=True).start()

    def reiniciar_para_actualizar():
        avisos = []
        if pest:
            avisos.append(f"Se van a cerrar las {len(pest)} pestaña(s) abiertas.")
        if app["ocupado"] or imp["proc"] is not None:
            messagebox.showinfo(NOMBRE, "Esperá a que termine el proceso o la impresión, y después reiniciá.")
            return
        if avisos and not messagebox.askyesno(NOMBRE, "\n".join(avisos) + "\n\n¿Reiniciar ahora para actualizar?"):
            return
        for t_ in list(pest):
            if not confirmar_cierre(t_):
                return
        try:
            lanzar_actualizador(act["nuevo"], act["tmp"])
        except Exception as e:
            messagebox.showerror(NOMBRE, f"No se pudo iniciar el actualizador:\n{e}")
            return
        salir_del_todo()


    # ================= color del tema (se aplica al volver a abrir)
    def elegir_tema(nombre):
        almacen.datos["tema"] = nombre
        almacen.guardar()
        for n_, b_ in botones_color_tema.items():
            b_.configure(border_color=C["acento"] if n_ == nombre else C["tarjeta"])
        if nombre == tema_actual:
            v_aviso_tema.set("Cada color tiene su versión clara y oscura (según el Modo de arriba).")
            b_reiniciar_tema.grid_forget()
        else:
            v_aviso_tema.set(f"«{nombre}» se aplica al volver a abrir PdFOL.")
            b_reiniciar_tema.grid(row=1, column=1, sticky="e", padx=(10, 16), pady=(0, 12))

    def reiniciar_pdfol():
        for t_ in list(pest):
            if not confirmar_cierre(t_):
                return
        import subprocess
        try:  # se suelta la «instancia unica» antes, asi el nuevo PdFOL no se la pasa a este
            if instancia not in (None, False):
                instancia.close()
        except Exception:
            pass
        cmd = [sys.executable] + ([] if getattr(sys, "frozen", False) else [os.path.abspath(__file__)])
        try:
            subprocess.Popen(cmd, close_fds=True)
        except Exception as e:
            messagebox.showerror(NOMBRE, f"No se pudo volver a abrir PdFOL:\n{e}")
            return
        salir_del_todo()


    # ================= menu del husky (arriba a la izquierda)
    def menu_husky():
        m_ = menu_contextual()
        m_.add_titulo(f"{NOMBRE} {VERSION}  ·  by {AUTOR}")
        if app.get("hay_nueva") and act.get("info"):
            m_.add_command(label=f"Actualizar a {act['info']['tag']}", command=lambda: ofrecer_version(act["info"]),
                           punto="#F97316")
        m_.add_command(label="Buscar actualizaciones", command=lambda: buscar_actualizacion(manual=True))
        m_.add_command(label="Novedades de esta versión", command=novedades)
        m_.add_separator()
        m_.add_command(label="Ayuda y atajos", command=ayuda_general, acelerador="F1")
        m_.add_command(label="Acerca de PdFOL", command=acerca_de)
        app["menu_logo"] = True
        dibujar_lateral()
        m_.tk_popup(superior.winfo_rootx() + 12, superior.winfo_rooty() + px(36) - 4)

        def vigilar():  # se quita el resaltado del logo cuando se cierra el menu
            if MenuPdfol.abierto is m_:
                raiz.after(150, vigilar)
            else:
                app["menu_logo"] = False
                dibujar_lateral()
        raiz.after(150, vigilar)

    def novedades():
        ventana_novedades(f"Novedades de {NOMBRE}", CAMBIOS)

    def ventana_novedades(titulo, secciones, botones=()):
        """Ventanita con el historial de cambios, con el estilo de PdFOL."""
        w = ctk.CTkToplevel(raiz)
        w.title(titulo)
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        cab = ctk.CTkFrame(w, fg_color="transparent")
        cab.pack(fill="x", padx=22, pady=(18, 8))
        ctk.CTkLabel(cab, text="", image=ctk.CTkImage(icono_husky(40 * 3), size=(40, 40))).pack(side="left", padx=(0, 10))
        ctk.CTkLabel(cab, text=titulo, font=F(17, "bold"), text_color=C["texto"]).pack(side="left")
        lista_cambios(w, secciones, alto=340).pack(fill="both", padx=22)
        pie = ctk.CTkFrame(w, fg_color="transparent")
        pie.pack(fill="x", padx=22, pady=16)
        boton(pie, "Cerrar", primario=not botones, ancho=100, command=w.destroy).pack(side="right", padx=(8, 0))
        for txt, cmd, prim in botones:
            boton(pie, txt, primario=prim, ancho=150, command=lambda c_=cmd: (w.destroy(), c_())).pack(
                side="right", padx=(8, 0))
        w.bind("<Escape>", lambda _e: w.destroy())
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + (raiz.winfo_height() - w.winfo_reqheight()) // 3}")
        w.after(80, lambda: (_tenir_barra_titulo(w, modo_oscuro()), w.focus_force()))

    def lista_cambios(master, secciones, alto=220, ancho=460):
        caja = ctk.CTkScrollableFrame(master, fg_color=C["tarjeta"], corner_radius=12, border_width=1,
                                      border_color=C["borde"], width=ancho, height=alto,
                                      scrollbar_button_color=C["suave_h"], scrollbar_button_hover_color=C["borde"])
        for k_, (ver_, puntos) in enumerate(secciones):
            fila_ = ctk.CTkFrame(caja, fg_color="transparent")
            fila_.pack(fill="x", padx=10, pady=(12 if k_ == 0 else 16, 4))
            ctk.CTkLabel(fila_, text=f"{NOMBRE} {ver_}" if ver_ else "", font=F(14, "bold"),
                         text_color=C["texto"]).pack(side="left")
            if ver_ == VERSION:
                ctk.CTkLabel(fila_, text="  esta versión", font=F(11, "bold"), text_color=C["acento"]).pack(side="left")
            for p_ in puntos:
                f_ = ctk.CTkFrame(caja, fg_color="transparent")
                f_.pack(fill="x", padx=12, pady=1)
                ctk.CTkLabel(f_, text="•", font=F(12, "bold"), text_color=C["acento"], width=14).pack(side="left",
                                                                                                      anchor="n")
                ctk.CTkLabel(f_, text=p_, font=F(12), text_color=C["texto"], anchor="w", justify="left",
                             wraplength=ancho - 60).pack(side="left", fill="x")
        return caja

    def ayuda_general(*_):
        m_ = menu_contextual()
        m_.add_titulo("Atajos de PdFOL")
        for t_, a_ in (("Abrir PDF", "Ctrl+O"), ("Cerrar pestaña · Siguiente", "Ctrl+W · Ctrl+Tab"),
                       ("Buscar", "Ctrl+B · Ctrl+F"), ("Siguiente resultado", "Enter · F3"),
                       ("Copiar texto seleccionado", "Ctrl+C"), ("Seleccionar la página", "Ctrl+A"),
                       ("Acercar · Alejar", "Ctrl + rueda · Ctrl + / −"), ("Ajustar ancho", "Ctrl+0"),
                       ("Mover la hoja", "botón del medio · Mano"), ("Guardar resaltados", "Ctrl+S"),
                       ("Deshacer · Rehacer", "Ctrl+Z · Ctrl+Y"), ("Imprimir", "Ctrl+P"),
                       ("Más opciones", "clic derecho")):
            m_.add_command(label=t_, acelerador=a_)
        m_.tk_popup(superior.winfo_rootx() + 12, superior.winfo_rooty() + px(36) - 4)
        return "break"

    def acerca_de():
        w = ctk.CTkToplevel(raiz)
        w.title(f"Acerca de {NOMBRE}")
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        caja = ctk.CTkFrame(w, fg_color=C["tarjeta"], corner_radius=14, border_width=1, border_color=C["borde"])
        caja.pack(padx=18, pady=18)
        ctk.CTkLabel(caja, text="", image=ctk.CTkImage(icono_husky(96 * 3), size=(96, 96))).pack(pady=(20, 6))
        fila_ = ctk.CTkFrame(caja, fg_color="transparent")
        fila_.pack()
        ctk.CTkLabel(fila_, text=NOMBRE, font=F(24, "bold"), text_color=C["texto"]).pack(side="left")
        ctk.CTkLabel(fila_, text=" " + VERSION, font=F(14, "bold"), text_color=C["acento"]).pack(side="left", pady=(6, 0))
        ctk.CTkLabel(caja, text=f"by {AUTOR}", font=F(13, "bold"), text_color=C["texto"]).pack(pady=(2, 0))
        ctk.CTkLabel(caja, text="Visor de PDF · Aplanar · Foliar · Comprimir", font=F(12),
                     text_color=C["texto2"]).pack(pady=(2, 12))
        try:
            libs = f"PyMuPDF {fitz.VersionBind} · pikepdf {pikepdf.__version__} · CustomTkinter {ctk.__version__}"
        except Exception:
            libs = ""
        for t_ in (("Versión instalada" if es_instalado() else "Versión portable") + f": {VERSION}",
                   f"Perfiles: {almacen.ruta}", libs):
            if t_:
                ctk.CTkLabel(caja, text=t_, font=F(10), text_color=C["texto2"], wraplength=380,
                             justify="center").pack(padx=24)
        ctk.CTkLabel(caja, text="Novedades", font=F(13, "bold"), text_color=C["texto"], anchor="w").pack(
            fill="x", padx=24, pady=(14, 4))
        lista_cambios(caja, CAMBIOS, alto=190, ancho=400).pack(padx=20)
        pie = ctk.CTkFrame(caja, fg_color="transparent")
        pie.pack(pady=(14, 18))
        boton(pie, "Página de PdFOL", ancho=150,
              command=lambda: __import__("webbrowser").open(f"https://github.com/{REPO_GITHUB}")).pack(
            side="left", padx=4)
        boton(pie, "Cerrar", primario=True, ancho=100, command=w.destroy).pack(side="left", padx=4)
        w.bind("<Escape>", lambda _e: w.destroy())
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + (raiz.winfo_height() - w.winfo_reqheight()) // 3}")
        w.after(80, lambda: (_tenir_barra_titulo(w, modo_oscuro()), w.focus_force()))

    raiz.bind("<F1>", ayuda_general)

    # ================= «¿Abrir siempre con PdFOL?» (version instalada)
    def abrir_siempre_con_pdfol():
        if not es_instalado():
            messagebox.showinfo(NOMBRE, "Esto funciona en la versión instalada de PdFOL "
                                        "(PdFOL_v2.0_instalador.exe). El portable no se registra en Windows.")
            return
        if pdfol_abre_los_pdf():
            v_estado.set("PdFOL ya es el programa para abrir los PDF.")
            return
        if elegir_pdfol_para_pdf():
            messagebox.showinfo(NOMBRE, "Se abrió la ventana de Windows «Aplicaciones predeterminadas».\n\n"
                                        "Elegí PdFOL para «.pdf» (o tocá «Establecer predeterminado»).\n"
                                        "Windows pide que lo confirmes vos: ningún programa puede ponerse solo.")

    def preguntar_abrir_siempre():
        if not es_instalado() or pdfol_abre_los_pdf() or almacen.datos.get("preguntar_pdf") is False:
            return
        w = ctk.CTkToplevel(raiz)
        w.title(NOMBRE)
        w.configure(fg_color=C["fondo"])
        w.resizable(False, False)
        w.transient(raiz)
        cab = ctk.CTkFrame(w, fg_color="transparent")
        cab.pack(fill="x", padx=22, pady=(18, 6))
        ctk.CTkLabel(cab, text="", image=ctk.CTkImage(icono_husky(48 * 3), size=(48, 48))).pack(side="left", padx=(0, 12))
        ctk.CTkLabel(cab, text="¿Querés abrir siempre los PDF con PdFOL?", font=F(15, "bold"),
                     text_color=C["texto"]).pack(side="left")
        ctk.CTkLabel(w, text="Así, con doble clic en cualquier PDF se abre en PdFOL (en una pestaña nueva si ya "
                             "está abierto). Windows te va a pedir que lo confirmes.", font=F(12),
                     text_color=C["texto2"], wraplength=440, justify="left", anchor="w").pack(fill="x", padx=22)
        pie = ctk.CTkFrame(w, fg_color="transparent")
        pie.pack(fill="x", padx=22, pady=18)

        def resp(v_):
            w.destroy()
            if v_ == "si":
                abrir_siempre_con_pdfol()
            elif v_ == "nunca":
                almacen.datos["preguntar_pdf"] = False
                almacen.guardar()
        boton(pie, "Sí, elegir PdFOL", primario=True, ancho=150, command=lambda: resp("si")).pack(side="right",
                                                                                                    padx=(8, 0))
        boton(pie, "Ahora no", ancho=100, command=lambda: resp("luego")).pack(side="right", padx=(8, 0))
        boton(pie, "No volver a preguntar", ancho=170, command=lambda: resp("nunca")).pack(side="right")
        w.update_idletasks()
        w.geometry(f"+{raiz.winfo_rootx() + (raiz.winfo_width() - w.winfo_reqwidth()) // 2}"
                   f"+{raiz.winfo_rooty() + (raiz.winfo_height() - w.winfo_reqheight()) // 3}")
        w.after(80, lambda: (_tenir_barra_titulo(w, modo_oscuro()), w.focus_force()))


    # ================= instancia unica: los PDF abiertos con doble clic entran como pestanas
    def escuchar_instancias(srv):
        for rutas in recibir_instancia(srv):
            eventos.put(("abrir_externo", list(rutas or [])))

    if instancia not in (None, False):
        threading.Thread(target=escuchar_instancias, args=(instancia,), daemon=True).start()

    def ctypes_hwnd(w):
        import ctypes
        return ctypes.windll.user32.GetParent(w.winfo_id())

    def mirar_impresion():
        if imp["proc"] is None:
            return
        fin = False
        try:
            while True:
                tipo, v_ = imp["cola"].get_nowait()
                if tipo == "imp_prog":
                    barra.set(v_[0] / max(1, v_[1]))
                    v_detalle.set(f"Hoja {v_[0]} de {v_[1]}")
                elif tipo == "imp_fin":
                    v_estado.set(f"Impresión enviada: {v_} hoja(s).")
                    barra.set(1)
                    fin = True
                elif tipo == "imp_cancelado":
                    v_estado.set("Impresión cancelada.")
                    fin = True
                elif tipo == "imp_error":
                    v_estado.set("Error al imprimir")
                    messagebox.showerror(NOMBRE, f"No se pudo imprimir:\n{v_}")
                    fin = True
        except queue.Empty:
            pass
        if not fin and not imp["proc"].is_alive():
            fin = True
        if fin:
            imp["proc"] = None
            msg_ = v_estado.get()
            refrescar()
            v_estado.set(msg_)
        else:
            raiz.after(200, mirar_impresion)


    # ================= atajos
    raiz.bind("<Control-o>", abrir_archivos)
    raiz.bind("<Control-O>", abrir_archivos)
    raiz.bind("<Control-w>", lambda e: cerrar_pestana(vis["act"]) if vis["act"] is not None else None)
    raiz.bind("<Control-W>", lambda e: cerrar_pestana(vis["act"]) if vis["act"] is not None else None)
    raiz.bind("<Control-b>", enfocar_busqueda)
    raiz.bind("<Control-B>", enfocar_busqueda)
    raiz.bind("<Control-f>", enfocar_busqueda)
    raiz.bind("<Control-F>", enfocar_busqueda)
    raiz.bind("<Control-p>", abrir_imprimir)
    raiz.bind("<Control-P>", abrir_imprimir)
    raiz.bind("<Control-s>", guardar_resaltados_dialogo)
    raiz.bind("<Delete>", quitar_editado, add="+")
    raiz.bind("<Control-S>", guardar_resaltados_dialogo)
    raiz.bind("<F3>", lambda e: busq_mover(-1 if e.state & 0x1 else 1))
    raiz.bind("<Control-Tab>", lambda e: (activar_pestana((vis["act"] + 1) % len(pest)) if pest else None, "break")[1])
    e_buscar.bind("<Return>", lambda e: buscar_texto(e_buscar.get()))
    e_buscar.bind("<Shift-Return>", lambda e: busq_mover(-1))
    e_buscar.bind("<Escape>", lambda e: (busq_cerrar(), vista_activa().cv.focus_set()))
    logo_grande = foto_tk(icono_husky(110))
    V["girar_prev"].trace_add("write", lambda *_: (visor_pedir_dibujo(), mini_pedir_dibujo()))


    # ================================================== LOGICA
    TITULOS = {c: tt for c, tt, *_ in ICONOS}

    def mostrar_pagina(clave):
        if vis.get("ined"):  # v4.1: lo que se estaba escribiendo en la hoja queda puesto
            ined_terminar(True)
        asegurar_pagina(clave)
        if clave in EN_PANEL:  # Aplanar, Foliar y Comprimir van en el panel derecho del visor
            abrir_panel(clave)
            return
        if app.get("panel") and (clave not in ("visor", "organizar") or
                                 (clave == "organizar" and app["panel"] not in EN_PANEL)):
            cerrar_panel()  # el panel derecho solo acompana al visor (y a Organizar con sus procesos)
        for k, w in paginas.items():
            w.grid_forget()
        if clave == "visor":  # el documento usa todo el espacio (sin titulo)
            titulo.grid_remove()
            paginas[clave].grid(row=0, column=0, rowspan=2, sticky="nsew")
        else:
            titulo.grid()
            paginas[clave].grid(row=1, column=0, sticky="nsew", padx=0, pady=(0, 0))
            titulo.configure(text=TITULOS[clave])
        app["pagina"] = clave
        if clave == "visor":  # la barra del visor vive en la fila de las pestanas
            pass
        else:
            pass
        dibujar_lateral()
        columna_izquierda()
        if clave == "organizar":
            raiz.after_idle(org_entrar)
        elif clave == "visor":
            vis["ult"] = vis["ult_mini"] = None
            raiz.after_idle(visor_dibujar)
            raiz.after_idle(mini_dibujar)

    def entero(v, defecto, minimo=0):
        try:
            return max(minimo, int(float(v.get().replace(",", "."))))
        except Exception:
            return defecto

    def decimal(v, defecto, lo, hi):
        try:
            return min(hi, max(lo, float(v.get().replace(",", "."))))
        except Exception:
            return defecto

    def cfg_folio():
        c = folio_por_defecto()
        c["inicio"] = entero(V["inicio"], 1, 0)
        c["digitos"] = min(10, entero(V["digitos"], 4, 1))
        c["desde"] = entero(V["desde"], 1, 1)
        c["hasta"] = entero(V["hasta"], None, 1) if V["hasta"].get().strip() else None
        c["con_total"] = V["formato"].get() == "Número / total"
        pr = V["prefijo"].get()
        c["prefijo"] = "" if pr == "Sin texto" else (V["prefijo_txt"].get() if pr == "Escribir" else pr)
        c["fuente"] = V["fuente"].get()
        c["tam"] = decimal(V["tam"], 12.0, 2, 200)
        c["negrita"] = V["negrita"].get()
        c["color"] = app["color"]
        c["posicion"] = V["pos"].get()
        c["margen_h_mm"] = decimal(V["mh"], 10.0, -300, 300)
        c["margen_v_mm"] = decimal(V["mv"], 10.0, 0, 300)
        return c

    # ---------------- perfiles: capturar / aplicar configuracion
    CLAVES_PERFIL = ["apl", "fol", "comp", "dpi", "texto", "nucleos", "nivel", "inicio", "digitos", "desde",
                     "hasta", "formato", "prefijo", "prefijo_txt", "fuente", "tam", "negrita", "pos", "mh", "mv"]

    def capturar():
        d = {k: V[k].get() for k in CLAVES_PERFIL}
        d["color"] = list(app["color"])
        return d

    def aplicar(d):
        app["cargando"] = True
        try:
            for k in CLAVES_PERFIL:
                if k in d:
                    if k == "fuente" and d[k] not in fuentes:
                        continue
                    if k == "nucleos" and d[k] != "Automático" and int(d[k]) > (os.cpu_count() or 1):
                        V[k].set("Automático")
                        continue
                    V[k].set(d[k])
            if "color" in d:
                poner_color(tuple(d["color"]), refrescar_prev=False)
        finally:
            app["cargando"] = False
        refrescar()
        actualizar_ejemplo()

    def nombre_perfil(i):
        pr = almacen.perfiles[i]
        return pr.get("nombre") if pr else None

    def refrescar_perfiles():
        for i, (num, nom, uso, bc, bg, br, be) in enumerate(filas_perfil):
            pr = almacen.perfiles[i]
            if pr:
                nom.configure(text=pr.get("nombre", f"Perfil {i + 1}"), text_color=C["texto"])
                num.configure(fg_color=C["acento"], text_color="#FFFFFF")
            else:
                nom.configure(text="Vacío", text_color=C["texto2"])
                num.configure(fg_color=C["suave"], text_color=C["texto2"])
            uso.configure(text="● En uso" if app["perfil"] == i and pr else "")
            for b in (bc, br, be):
                b.configure(state="normal" if pr else "disabled")
        i = app["perfil"]
        v_perfil_lbl.set(f"Perfil: {nombre_perfil(i)}" if i is not None and nombre_perfil(i) else "")
        dibujar_lateral()

    def pedir_nombre(titulo_, inicial=""):
        """Ventanita propia (en español y con el estilo del programa)."""
        res = {"v": None}
        dlg = ctk.CTkToplevel(raiz, fg_color=C["tarjeta"])
        dlg.title(titulo_)
        dlg.resizable(False, False)
        dlg.transient(raiz)
        ctk.CTkLabel(dlg, text=titulo_, font=F(16, "bold"), text_color=C["texto"]).pack(anchor="w", padx=22, pady=(18, 2))
        ctk.CTkLabel(dlg, text="Nombre del perfil", font=F(12), text_color=C["texto2"]).pack(anchor="w", padx=22)
        vn = tk.StringVar(value=inicial)
        e = entrada(dlg, vn, 300)
        e.pack(padx=22, pady=(6, 16))
        fila_b = ctk.CTkFrame(dlg, fg_color="transparent")
        fila_b.pack(fill="x", padx=22, pady=(0, 18))

        def aceptar(_=None):
            res["v"] = vn.get().strip()[:40] or None
            dlg.destroy()

        boton(fila_b, "Guardar", primario=True, ancho=100, command=aceptar).pack(side="right")
        boton(fila_b, "Cancelar", ancho=100, command=dlg.destroy).pack(side="right", padx=(0, 8))
        e.bind("<Return>", aceptar)
        dlg.bind("<Escape>", lambda _: dlg.destroy())
        dlg.update_idletasks()
        x = raiz.winfo_rootx() + (raiz.winfo_width() - dlg.winfo_width()) // 2
        y = raiz.winfo_rooty() + (raiz.winfo_height() - dlg.winfo_height()) // 3
        dlg.geometry(f"+{max(0, x)}+{max(0, y)}")
        dlg.after(80, lambda: (_tenir_barra_titulo(dlg, modo_oscuro()), e.focus_set(), e.select_range(0, "end")))
        try:
            dlg.grab_set()
        except Exception:
            pass
        raiz.wait_window(dlg)
        return res["v"]

    def perfil_guardar(i):
        pr = almacen.perfiles[i]
        if pr and not messagebox.askyesno(NOMBRE, f"¿Reemplazar el perfil «{pr.get('nombre')}» con la configuración actual?"):
            return
        nombre = pr.get("nombre") if pr else pedir_nombre("Guardar perfil", f"Perfil {i + 1}")
        if not nombre:
            return
        almacen.perfiles[i] = {"nombre": nombre, "config": capturar(), "guardado": time.strftime("%Y-%m-%d %H:%M")}
        almacen.datos["ultimo"] = i
        app["perfil"] = i
        if not almacen.guardar():
            messagebox.showerror(NOMBRE, f"No se pudo guardar el archivo de perfiles:\n{almacen.ruta}")
        refrescar_perfiles()
        v_estado.set(f"Perfil «{nombre}» guardado.")

    def perfil_cargar(i):
        pr = almacen.perfiles[i]
        if not pr:
            return
        aplicar(pr.get("config", {}))
        app["perfil"] = i
        almacen.datos["ultimo"] = i
        almacen.guardar()
        refrescar_perfiles()
        v_estado.set(f"Perfil «{pr.get('nombre')}» cargado.")

    def perfil_renombrar(i):
        pr = almacen.perfiles[i]
        if not pr:
            return
        n = pedir_nombre("Renombrar perfil", pr.get("nombre", ""))
        if n:
            pr["nombre"] = n
            almacen.guardar()
            refrescar_perfiles()

    def perfil_eliminar(i):
        pr = almacen.perfiles[i]
        if pr and messagebox.askyesno(NOMBRE, f"¿Eliminar el perfil «{pr.get('nombre')}»?"):
            almacen.perfiles[i] = None
            if app["perfil"] == i:
                app["perfil"] = None
                almacen.datos["ultimo"] = None
            almacen.guardar()
            refrescar_perfiles()


    # ---------------- color / posicion / ejemplo / vista previa
    def poner_color(rgb, refrescar_prev=True):
        app["color"] = tuple(int(x) for x in rgb)
        for b, c_ in puntos_color:
            b.configure(border_width=3 if tuple(c_) == app["color"] else 0)
        if refrescar_prev:
            actualizar_ejemplo()

    def color_otro():
        res = colorchooser.askcolor(color="#%02x%02x%02x" % app["color"], title="Color del folio")
        if res and res[0]:
            poner_color(res[0])

    def marcar_posicion(*_):
        for n_, b in botones_pos.items():
            b.configure(fg_color=C["acento"] if n_ == V["pos"].get() else C["suave_h"])

    def total_folios(c):
        n = app["n_paginas"]
        return None if n is None else len(rango_folio(c, n))

    def textos_ejemplo():
        c = cfg_folio()
        cant = total_folios(c)
        total = c["inicio"] + (cant - 1 if cant else 0) if cant is not None else c["inicio"] + 1999
        return c, texto_folio(c, c["inicio"], total)

    def actualizar_ejemplo(*_):
        if app["cargando"]:
            return
        _, txt = textos_ejemplo()
        v_ejemplo.set(txt)
        visor_pedir_dibujo()  # el folio se ve en vivo en el documento
        if app["prev_job"]:
            raiz.after_cancel(app["prev_job"])
        app["prev_job"] = raiz.after(220, pedir_preview)

    def pedir_preview():
        app["prev_job"] = None
        if lbl_mini is None:  # v2.5: el panel Foliar todavia no esta armado (nadie la ve)
            return
        c, txt = textos_ejemplo()
        ruta = V["ruta"].get().strip().strip('"')
        ruta = ruta if os.path.isfile(ruta) else None
        idx = c["desde"] - 1
        if app["n_paginas"]:
            idx = min(idx, app["n_paginas"] - 1)
        prev.pedir(ruta, idx, c, txt, V["girar_prev"].get())
        if ruta:
            v_prev_info.set(f"Página {idx + 1}: primer folio." + ("" if V["fol"].get() else "\nActivá «Foliar páginas» para aplicarlo."))
        else:
            v_prev_info.set("Ejemplo sobre una hoja A4. Elegí un PDF para verlo sobre tu documento.")

    # ---------------- estado general
    def refrescar(*_):
        if app["cargando"]:
            return
        ocup = app["ocupado"]

        def act(w, si):
            try:
                w.configure(state="normal" if si else "disabled")
            except Exception:
                pass

        for w in ctrl_apl:
            act(w, not ocup and V["apl"].get())
        for w in ctrl_fol:
            act(w, not ocup and V["fol"].get())
        act(e_pref, not ocup and V["fol"].get() and V["prefijo"].get() == "Escribir")
        for w in ctrl_comp:
            act(w, not ocup and V["comp"].get())
        for w in (b_buscar, sw_apl, sw_fol, sw_comp):
            act(w, not ocup)
        hay = bool(V["ruta"].get().strip())
        algo = V["apl"].get() or V["fol"].get() or V["comp"].get()
        organizado = org_activo()
        act(b_analizar, not ocup and V["apl"].get() and hay and not organizado)
        listo = (hay and algo and (not V["apl"].get() or app["scores"] is not None)) or (organizado and algo)
        act(b_procesar, listo and not ocup)
        act(b_cancelar, ocup or imp["proc"] is not None)
        act(b_carpeta, (not ocup) and bool(app["salida"]))
        v_ayuda_niv.set(AYUDA_NIVEL.get(V["nivel"].get(), ""))
        marcar_posicion()
        try:
            org_info()  # botones del organizador (Limpiar todo, Abrir…) segun el estado
        except NameError:
            pass
        if not ocup and not app["salida"]:
            if not hay:
                v_estado.set("Elegí un PDF para empezar.")
            elif not algo:
                v_estado.set("Activá al menos una opción: Aplanar, Foliar o Comprimir.")
            elif organizado:
                v_estado.set(f"Listo. «Procesar» trabaja sobre las {len(org['orden'])} páginas organizadas.")
            elif V["apl"].get() and app["scores"] is None:
                v_estado.set("Presioná «Analizar» para detectar los planos pesados.")
            else:
                v_estado.set("Listo. Presioná «Procesar».")

    def ocupar(si):
        app["ocupado"] = si
        refrescar()

    def nuevo_archivo(r_):
        """En la v2.0 cada PDF va en su pestana (v2.4: siempre se ve primero en el visor)."""
        return abrir_pestana(r_)

    def _abrir_documento(r_):
        V["ruta"].set(os.path.normpath(r_))
        app.update(scores=None, salida=None, n_paginas=None)
        v_detalle.set("")
        barra.set(0)
        v_info_apl.set("Presioná «Analizar» para detectar los planos pesados.")
        try:
            app["n_paginas"] = contar_paginas(V["ruta"].get())
            mb = os.path.getsize(V["ruta"].get()) / 1048576
            app["listas"] = leer_listas(V["ruta"].get())
            extra_ = ""
            if app["listas"]:
                extra_ = (f"  ·  {len(app['listas'])} ya aplanadas y comprimidas (no se repiten)"
                          if len(app["listas"]) < app["n_paginas"] else "  ·  ya aplanado y comprimido (no se repite)")
            v_info_doc.set(f"{app['n_paginas']} páginas  ·  {mb:.1f} MB" + extra_)
        except Exception:
            v_info_doc.set("No se pudo leer el documento.")
        refrescar()
        actualizar_ejemplo()

    def buscar():
        r_ = filedialog.askopenfilename(title="Elegí el PDF", filetypes=[("PDF", "*.pdf")])
        if r_:
            abrir_pestana(r_)

    def ruta_valida():
        ruta = V["ruta"].get().strip().strip('"')
        if not os.path.isfile(ruta):
            messagebox.showerror(NOMBRE, "No encuentro ese archivo PDF.")
            return None
        return ruta

    def paginas_elegidas():
        scores, umbral = app["scores"], app["umbral"]
        n = len(scores)
        pes = {i for i, s in enumerate(scores) if s >= umbral}
        pes |= parsear_paginas(V["extra"].get(), n)
        pes -= parsear_paginas(V["excluir"].get(), n)
        pes -= app.get("listas") or set()
        return pes

    def analizar_click():
        ruta = ruta_valida()
        if not ruta:
            return
        app.update(ruta=ruta, salida=None)
        cancelar.clear()
        ocupar(True)
        barra.set(0)
        v_estado.set("Analizando páginas…")
        v_detalle.set("")

        def hilo():
            try:
                eventos.put(("analisis", analizar(ruta, lambda h, t_: eventos.put(("prog_an", h, t_)), cancelar)))
            except Cancelado:
                eventos.put(("cancelado",))
            except Exception as e:
                eventos.put(("error", f"No se pudo analizar el PDF:\n{e}"))
        threading.Thread(target=hilo, daemon=True).start()

    def procesar_click():
        t_ = pest_activa()
        if t_ and not preguntar_resaltes(set(org.get("fuentes") or []) | {t_["ruta"]}, "procesar"):
            return
        if org_activo():
            org_procesar_guardar()
            return
        ruta = ruta_valida()
        if not ruta:
            return
        app["listas"] = leer_listas(ruta)
        pes = set()
        if V["apl"].get():
            if app["scores"] is None or app["ruta"] != ruta:
                messagebox.showinfo(NOMBRE, "Primero presioná «Analizar».")
                return
            try:
                pes = paginas_elegidas()
            except ValueError:
                messagebox.showerror(NOMBRE, "Revisá las páginas a agregar o excluir (ej.: 15, 20-35).")
                return
            if not pes and not (V["fol"].get() or V["comp"].get()):
                messagebox.showinfo(NOMBRE, "No hay planos para aplanar. Agregá páginas a mano o activá otra opción.")
                return
        folio = None
        if V["fol"].get():
            folio = cfg_folio()
            n = app["n_paginas"] or contar_paginas(ruta)
            if folio["desde"] > n or (folio["hasta"] and folio["hasta"] < folio["desde"]):
                messagebox.showerror(NOMBRE, f"Revisá el rango de páginas a foliar (el documento tiene {n} páginas).")
                return
            if V["prefijo"].get() == "Escribir" and not V["prefijo_txt"].get().strip():
                if not messagebox.askyesno(NOMBRE, "Elegiste «Escribir» pero el texto está vacío. ¿Foliar solo con el número?"):
                    return
        compresion = NIVELES_UI[V["nivel"].get()] if V["comp"].get() else None
        dpi = int(V["dpi"].get())
        nuc = None if V["nucleos"].get() == "Automático" else int(V["nucleos"].get())
        texto = V["texto"].get()
        cancelar.clear()
        app["salida"] = None
        ocupar(True)
        barra.set(0)
        v_detalle.set("")
        v_estado.set("Iniciando…")

        def hilo():
            try:
                res = procesar(ruta, pes, dpi=dpi, nucleos=nuc, texto=texto, folio=folio, compresion=compresion,
                               progreso=lambda h, t_, eta: eventos.put(("prog", h, t_, eta)),
                               estado=lambda m: eventos.put(("estado", m)),
                               cancelar=cancelar, scores=app["scores"], ya_listas=app.get("listas") or set(),
                               marcar_listas=V["apl"].get() and V["comp"].get())
                eventos.put(("fin", res))
            except Cancelado:
                eventos.put(("cancelado",))
            except Exception as e:
                eventos.put(("error", f"Ocurrió un error durante el proceso:\n{e}"))
        threading.Thread(target=hilo, daemon=True).start()

    def cancelar_click():
        if imp["proc"] is not None and not app["ocupado"]:
            if messagebox.askyesno(NOMBRE, "¿Cancelar la impresión?"):
                imp["cancelar"].set()
                v_estado.set("Cancelando la impresión…")
            return
        if messagebox.askyesno(NOMBRE, "¿Cancelar el proceso? El original no se modifica."):
            cancelar.set()
            v_estado.set("Cancelando…")

    def abrir_carpeta():
        s = app["salida"]
        if not s:
            return
        try:
            if os.name == "nt":
                import subprocess
                subprocess.Popen(["explorer", "/select,", s])
            else:
                import webbrowser
                webbrowser.open(os.path.dirname(s))
        except Exception:
            pass

    # ---------------- apariencia
    def cambiar_apariencia(*_):
        m = V["apariencia"].get()
        ctk.set_appearance_mode({"Claro": "light", "Oscuro": "dark"}.get(m, "system"))
        for n_, b in botones_tema.items():
            b.configure(border_color=C["acento"] if n_ == m else C["tarjeta"])
        almacen.datos["apariencia"] = m
        almacen.guardar()
        raiz.after(60, revisar_modo)

    def revisar_modo():
        actual = modo_oscuro()
        if actual != app["modo_actual"]:
            app["modo_actual"] = actual
            dibujar_lateral()
            _tenir_barra_titulo(raiz, actual)
            dibujar_pestanas()
            visor_pedir_dibujo()
            mini_pedir_dibujo()
            marcar_posicion()
            refrescar_perfiles()
            for b, c_ in puntos_color:
                b.configure(border_color=C["acento"])

    def vigilar_modo():  # para "Automático": seguir cambios de Windows
        revisar_modo()
        raiz.after(1500, vigilar_modo)

    # ---------------- eventos del proceso
    # ================= v3.0: acciones de la cinta, la barra de abajo y el riel
    def cinta_deshacer():
        if app["pagina"] == "organizar":
            org_deshacer()
        elif hist["atras"]:
            deshacer_edicion()
        elif vis["res_pila"]:
            deshacer_resaltado()
        else:
            v_estado.set("No hay nada para deshacer.")

    def cinta_herr(h_):
        if app["pagina"] != "visor":
            mostrar_pagina("visor")
        if app.get("panel") in ("texto", "firmar"):
            cerrar_panel()
        v_herr.set(h_)
        cambiar_herramienta()

    def zoom_cinta(valor):
        if app["pagina"] != "visor":
            mostrar_pagina("visor")
        v_ = vista_activa()
        if v_ and v_.t:
            v_.poner_zoom(valor)
        almacen.datos["zoom_inicial"] = valor  # el proximo PDF abre igual

    def girar_vista(d):
        """Gira como se ve el documento (no cambia el PDF; para eso, Organizar › Girar)."""
        t_ = pest_activa()
        if not t_:
            v_estado.set("Abrí un PDF para girarlo.")
            return
        if app["pagina"] != "visor":
            mostrar_pagina("visor")
        t_["giro"] = (t_.get("giro", 0) + d) % 360
        for v_ in vistas:
            if v_.t is t_:
                v_.reanclar = v_.posicion() if v_.lay else None
                v_.lay_k = None
        v_estado.set(f"Vista girada {t_['giro']}° (solo la vista; el PDF no cambia)." if t_["giro"] else
                     "Vista derecha.")
        visor_pedir_dibujo()
        dibujar_cinta()

    def modo_vista(m_):
        t_ = pest_activa()
        if not t_:
            return
        if app["pagina"] != "visor":
            mostrar_pagina("visor")
        t_["modo_vista"] = m_
        for v_ in vistas:
            if v_.t is t_:
                v_.reanclar = v_.posicion() if v_.lay else None
                v_.lay_k = None
        visor_pedir_dibujo()
        dibujar_cinta()

    def cinta_panel(clave):
        if app["pagina"] in ("visor", "organizar") and app.get("panel") == clave:
            cerrar_panel()  # tocarla de nuevo la cierra
        else:
            abrir_panel(clave)

    def cinta_texto(modo_):
        abrir_panel("texto")
        try:
            v_tmodo.set(modo_)
            ayuda_texto()
        except Exception:
            pass

    def cinta_pagina(clave):
        if app["pagina"] == clave:
            mostrar_pagina("visor")  # tocar de nuevo vuelve al documento
        else:
            mostrar_pagina(clave)

    def cinta_unir():
        mostrar_pagina("organizar")
        raiz.after(120, org_unir)

    def pantalla_completa(*_):
        app["completa"] = not app.get("completa")
        si = app["completa"]
        try:
            raiz.attributes("-fullscreen", si)
        except Exception:
            pass
        for w_ in (superior, barra_pest):
            if si:
                w_.grid_remove()
            else:
                w_.grid()
        if si:
            v_estado.set("Pantalla completa: Esc o F11 para salir.")
        raiz.after(80, redibujar_todo)
        dibujar_cinta()

    raiz.bind("<F11>", pantalla_completa)
    raiz.bind("<Escape>", lambda e: pantalla_completa() if app.get("completa") else None, add="+")

    # riel de la izquierda
    def _riel_img(clave):
        return ctk.CTkImage(_icono(clave, C["tarjeta"][0], 66, glifo=_hex(C["texto2"][0]), sin_fondo=True),
                            _icono(clave, C["tarjeta"][1], 66, glifo=_hex(C["texto2"][1]), sin_fondo=True),
                            size=(20, 20))
    for k_r, f_r, tip_r in (("miniaturas", lambda: alternar_miniaturas(), "Miniaturas"),
                            ("marcadores", lambda: alternar_marcadores(), "Marcadores"),
                            ("buscar", lambda: enfocar_busqueda(), "Buscar (Ctrl+F)")):
        riel_b[k_r] = ctk.CTkButton(riel, text="", width=32, height=32, corner_radius=8, image=_riel_img(k_r),
                                    fg_color="transparent", hover_color=C["suave"], command=f_r)
        riel_b[k_r].pack(padx=4, pady=(10 if k_r == "miniaturas" else 3, 0))
    ctk.CTkFrame(riel, width=1, fg_color=C["borde"], corner_radius=0).place(relx=1.0, x=-1, rely=0, relheight=1)

    # todo lo que depende del estado se revisa 4 veces por segundo (barato: solo si cambio algo)
    estado_ui = {"firma": None}

    def revisar_ui():
        try:
            v_ = vista_activa()
            t_ = pest_activa()
            lay_ = v_.lay if (v_ and v_.t) else None
            if lay_:
                n_ = len(lay_["pags"])
                v_tot_inf.set(f"de {n_}")
                if raiz.focus_get() is not e_pag_inf._entry:
                    v_pag_inf.set(str(v_.pag + 1))
                if raiz.focus_get() is not e_pag_bar._entry:
                    v_pag_bar.set(str(v_.pag + 1))
                v_tot_bar.set(f"/ {n_}")
                pct_ = v_.pct_actual()
                v_pct_inf.set(f"{pct_:.0f} %")
                v_pct_bar.set(f"{pct_:.0f} %")
                if not zoom_inf["arrastrando"] and barra_inf.winfo_ismapped():  # v4.0: no redibujar lo oculto
                    s_zoom.set(max(0.0, min(1.0, math.log(max(10, min(800, pct_)) / 10) / math.log(80))))
            else:
                v_tot_inf.set("")
                v_pag_inf.set("")
                v_pct_inf.set("")
            modo_ = (t_ or {}).get("modo_vista", "continua")
            lado_ = app.get("lado_izq", "minis") if almacen.datos.get("miniaturas") is not False else None
            busca = bool(caja_busq.winfo_manager())
            hay_vis = any(w_.winfo_manager() for w_ in barra_vis.winfo_children())
            firma_ = (modo_, lado_, hay_vis, vis["comp"], app["pagina"], app.get("panel"), app["cinta"],
                      n_resaltes(), v_herr.get(), bool(vis["modo_res"]), id(t_), (t_ or {}).get("giro", 0),
                      v_.zoom if v_ else None, bool(V["girar_prev"].get()), modo_oscuro(), len(pest), busca,
                      app.get("vista_top"), v_tot_bar.get(), v_pct_bar.get(), bool(app.get("completa")))
            if firma_ != estado_ui["firma"]:
                estado_ui["firma"] = firma_
                for m_, b_ in (b_modos.items() if barra_inf.winfo_ismapped() else ()):
                    b_.configure(fg_color=C["lat_sel"] if m_ == modo_ else C["suave"])
                for k_r, b_ in riel_b.items():
                    b_.configure(fg_color=C["suave"] if k_r == lado_ else "transparent")
                if hay_vis and app["pagina"] == "visor":
                    barra_vis.grid(row=0, column=0, columnspan=2, sticky="ew", padx=(8, 14), pady=(8, 0))
                else:
                    barra_vis.grid_remove()
                for v__ in vistas:
                    if vis["comp"]:
                        v__.bar.grid()
                    else:
                        v__.bar.grid_remove()
                mostrar_inicio()
                dibujar_cinta()
                dibujar_riel_der()
                dibujar_superior()
        except Exception:
            pass
        raiz.after(250, revisar_ui)

    raiz.after(400, revisar_ui)

    def procesar_eventos():
        try:
            while True:
                ev = eventos.get_nowait()
                tipo = ev[0]
                if tipo == "preview":
                    _, mini, zoom, _n, (papel_, acostada_) = ev
                    if V["ruta"].get().strip():
                        mm_ = float(decimal(V["tam"], 12.0, 2, 200)) * 25.4 / 72
                        v_prev_info.set(v_prev_info.get().split("\n")[0] + f"\nHoja {'horizontal' if acostada_ else 'vertical'}, "
                                        f"se imprime en {papel_}. Folio en papel: {decimal(V['tam'], 12.0, 2, 200):g} pt (≈{mm_:.1f} mm), "
                                        "igual en todas las hojas.")
                    if lbl_mini is not None:
                        lbl_mini.configure(image=ctk.CTkImage(mini, size=mini.size), width=mini.width, height=mini.height)
                        lbl_zoom.configure(image=ctk.CTkImage(zoom, size=zoom.size), width=zoom.width, height=zoom.height)
                elif tipo == "abrir_externo":
                    for r_ in ev[1]:
                        abrir_pestana(r_)
                    try:
                        raiz.deiconify()
                        raiz.lift()
                        raiz.attributes("-topmost", True)
                        raiz.after(300, lambda: raiz.attributes("-topmost", False))
                        raiz.focus_force()
                    except Exception:
                        pass
                    raiz.after(120, redibujar_todo)  # v2.5: si estaba minimizado, que no quede la hoja anterior
                elif tipo == "version":
                    _, info_, manual_ = ev
                    if hay_version_nueva(info_):
                        ofrecer_version(info_)
                        if manual_:
                            v_estado.set(f"Hay una versión nueva: {info_['tag']}.")
                    elif manual_:
                        v_estado.set(f"Tenés la última versión ({VERSION}).")
                        messagebox.showinfo(NOMBRE, f"Tenés la última versión de PdFOL ({VERSION}).")
                elif tipo == "version_error":
                    if ev[2]:
                        v_estado.set("No se pudo revisar si hay actualizaciones.")
                        messagebox.showinfo(NOMBRE, "No se pudo revisar si hay actualizaciones "
                                                    "(sin internet o GitHub no responde).\n\n" + ev[1][:200])
                elif tipo == "act_prog":
                    _, h_, t_ = ev
                    pct_ = int(h_ * 100 / t_) if t_ else 0
                    v_franja.set(f"Descargando PdFOL {act['info']['tag']}… {pct_} %  ({h_ / 1048576:.1f} MB)")
                    if not app["ocupado"] and imp["proc"] is None:
                        barra.set(h_ / t_ if t_ else 0)
                        v_estado.set(f"Descargando la actualización… {pct_} %")
                elif tipo == "act_listo":
                    act["nuevo"], act["bajando"] = ev[1], False
                    if not app["ocupado"]:
                        barra.set(1)
                        v_estado.set("Actualización descargada y comprobada (SHA256).")
                    franja_mostrar(f"PdFOL {act['info']['tag']} está listo para instalarse.",
                                   [("Reiniciar ahora", reiniciar_para_actualizar, True), ("Después", franja_ocultar, False)])
                elif tipo == "act_error":
                    act["bajando"] = False
                    franja_ocultar()
                    if ev[1] is None:
                        v_estado.set("Descarga cancelada. Seguís con tu versión.")
                    else:
                        v_estado.set("No se pudo actualizar. Seguís con tu versión.")
                        messagebox.showerror(NOMBRE, f"No se pudo actualizar:\n{ev[1]}")
                elif tipo == "preview_error":
                    v_prev_info.set("No se pudo generar la vista previa: " + ev[1])
                elif tipo == "prog_an":
                    _, h, t_ = ev
                    barra.set(h / t_)
                    v_detalle.set(f"Página {h} de {t_}")
                elif tipo == "analisis":
                    app["scores"], app["umbral"] = ev[1]
                    app["n_paginas"] = len(app["scores"])
                    ocupar(False)
                    pes = sorted(paginas_elegidas())
                    lista = ", ".join(str(q + 1) for q in pes[:40]) + (" …" if len(pes) > 40 else "")
                    msg = f"Se detectaron {len(pes)} planos pesados de {app['n_paginas']} páginas."
                    v_estado.set(msg)
                    v_info_apl.set(msg + ("\nPáginas: " + lista if pes else "\nPodés agregar páginas a mano."))
                    v_detalle.set(("Páginas: " + lista) if pes else "")
                    barra.set(1)
                    actualizar_ejemplo()
                elif tipo == "estado":
                    v_estado.set(ev[1])
                elif tipo == "prog":
                    _, h, t_, eta = ev
                    barra.set(h / t_)
                    v_detalle.set(f"Plano {h} de {t_}  ·  faltan aprox. {fmt_tiempo(eta)}")
                elif tipo == "fin":
                    r_ = ev[1]
                    app["salida"] = r_["salida"]
                    ocupar(False)
                    barra.set(1)
                    v_estado.set("¡Listo!")
                    partes = []
                    if r_["planos"]:
                        partes.append(f"{r_['planos']} planos aplanados ({r_['nucleos']} núcleos)")
                    if r_["foliadas"]:
                        partes.append(f"{r_['foliadas']} páginas foliadas")
                    if r_["compresion"]:
                        partes.append(f"compresión {NOMBRES_NIVEL[r_['compresion']].lower()}")
                    partes.append(f"{fmt_tiempo(r_['segundos'])}")
                    partes.append(f"{r_['mb_entrada']:.1f} MB → {r_['mb_salida']:.1f} MB")
                    v_detalle.set("  ·  ".join(partes) + f"\n{r_['salida']}")
                    refrescar()
                elif tipo == "cancelado":
                    ocupar(False)
                    barra.set(0)
                    v_estado.set("Proceso cancelado.")
                    v_detalle.set("No se generó ningún archivo.")
                elif tipo == "error":
                    ocupar(False)
                    v_estado.set("Error")
                    messagebox.showerror(NOMBRE, ev[1])
        except queue.Empty:
            pass
        raiz.after(120, procesar_eventos)

    def salir_del_todo():
        """Cierra PdFOL por completo: corta las colas con los procesos de dibujo (en Windows, esperar a que
        se vacien podia dejar el programa vivo y escondido) y termina sin esperas."""
        app["cerrando"] = True
        raiz.report_callback_exception = lambda *a: None
        try:
            if instancia not in (None, False):
                instancia.close()
        except Exception:
            pass
        detener_dibujantes()
        for q_ in (q_pag, q_min, q_bus, q_sal):
            try:
                q_.cancel_join_thread()
                q_.close()
            except Exception:
                pass
        try:
            raiz.destroy()
        except Exception:
            pass
        try:
            sys.stdout.flush()
        except Exception:
            pass
        os._exit(0)

    def al_cerrar():
        if app["ocupado"]:
            if not messagebox.askyesno(NOMBRE, "Hay un proceso en curso. ¿Cancelarlo y salir?"):
                return
            cancelar.set()
            raiz.after(1000, salir_del_todo)
            return
        for t_ in list(pest):  # cada documento con cambios pregunta si se guarda
            if not confirmar_cierre(t_):
                return
        if n_resaltes() and not preguntar_resaltes(None, "salir"):
            return
        app["cerrando"] = True
        try:  # recordar si quedo maximizada o en otro tamano
            maxi = raiz.state() == "zoomed" or (os.name != "nt" and bool(raiz.attributes("-zoomed")))
            if app.get("completa") or raiz.state() == "iconic":
                pass  # v3.0: en pantalla completa o minimizada no se guarda un tamano raro
            else:
                almacen.datos["ventana"] = "max" if maxi else raiz.geometry()
                almacen.datos["ventana_monitor"] = [raiz.winfo_rootx() + raiz.winfo_width() // 2,
                                                    raiz.winfo_rooty() + raiz.winfo_height() // 2]  # v4.2
            almacen.guardar()
        except Exception:
            pass
        salir_del_todo()

    # ---------------- conexiones
    prev = Previsualizador(eventos.put)
    prev.start()
    b_analizar.configure(command=analizar_click)
    b_procesar.configure(command=procesar_click)
    b_cancelar.configure(command=cancelar_click)
    b_carpeta.configure(command=abrir_carpeta)
    for k in ("apl", "fol", "comp", "nivel", "ruta", "prefijo"):
        V[k].trace_add("write", refrescar)
    for k in ("inicio", "digitos", "desde", "hasta", "formato", "prefijo", "prefijo_txt", "fuente", "tam",
              "negrita", "pos", "mh", "mv", "fol"):
        V[k].trace_add("write", actualizar_ejemplo)
    V["pos"].trace_add("write", marcar_posicion)
    V["apariencia"].trace_add("write", cambiar_apariencia)
    raiz.protocol("WM_DELETE_WINDOW", al_cerrar)

    # estado inicial: ultimo perfil usado
    ult = almacen.datos.get("ultimo")
    if isinstance(ult, int) and 0 <= ult < MAX_PERFILES and almacen.perfiles[ult]:
        aplicar(almacen.perfiles[ult].get("config", {}))
        app["perfil"] = ult
        V["fol"].set(False)  # v2.4: al abrir para ver, sin folio (se prende al unir o a mano)
    else:
        app["perfil"] = None
        poner_color((0, 0, 0), refrescar_prev=False)
    def mostrar_ventana():
        """Ventana lista: aparece (maximizada o como la dejaste) y se va el husky."""
        _tiempo("ventana visible")
        if not os.environ.get("PDFOL_PRUEBA"):
            geo_ = almacen.datos.get("ventana", "max")
            if geo_ != "max":
                try:
                    raiz.geometry(geo_)
                except Exception:
                    geo_ = "max"
            if geo_ == "max":  # v3.0: ya del tamano final, asi la hoja no aparece corrida y despues salta
                try:  # v4.2: en el monitor donde estaba la ultima vez
                    mx_, my_ = almacen.datos.get("ventana_monitor") or (raiz.winfo_screenwidth() // 2, 300)
                    a0_, b0_, a1_, b1_ = area_monitor(mx_, my_, raiz)
                    if a1_ - a0_ > 100000:
                        a0_, b0_, a1_, b1_ = 0, 0, raiz.winfo_screenwidth(), raiz.winfo_screenheight() - 80
                    raiz.geometry(f"{a1_ - a0_}x{b1_ - b0_}+{a0_}+{b0_}")
                except Exception:
                    pass
            raiz.deiconify()
            if geo_ == "max":
                maximizar()
            raiz.lift()
            raiz.focus_force()
        raiz.after(350, cerrar_pantalla_de_inicio)
        raiz.after(250, arrancar_procesos)
        # v4.0: las paginas y paneles se arman recien cuando se abren por primera vez (no todos al iniciar)
    raiz.after(150, iniciar_dibujantes)  # primero se muestra la ventana

    # v4.0: la basura de Python se junta SOLO aca, en el hilo de la ventana. Si el recolector corria en otro
    # hilo y liberaba letras o imagenes de Tk, la ventana se podia quedar pegada para siempre
    import gc
    gc.disable()

    def juntar_basura():
        try:
            gc.collect()
        finally:
            raiz.after(4000, juntar_basura)
    raiz.after(4000, juntar_basura)

    # ---- v4.0: cambio de monitor (otra escala: 100 % -> 150 %...). Se ajusta UNA vez, cuando la ventana ya
    # se solto y quedo quieta, sin volverla transparente
    def _boton_apretado():
        if os.name != "nt":
            return False
        try:
            import ctypes
            return bool(ctypes.windll.user32.GetAsyncKeyState(0x01) & 0x8000)
        except Exception:
            return False

    def ajustar_escala(w_, nueva):
        T_ = ctk.ScalingTracker
        T_.window_dpi_scaling_dict[w_] = nueva
        try:
            w_.block_update_dimensions_event()
        except Exception:
            pass
        try:
            T_.update_scaling_callbacks_for_window(w_)
        finally:
            try:
                w_.unblock_update_dimensions_event()
            except Exception:
                pass
        if w_ is not raiz:
            return
        escala["s"] = max(1.0, nueva * T_.widget_scaling)
        if escala["ts0"]:  # letras de los dibujos propios (en puntos) al tamano de la nueva pantalla
            try:
                raiz.tk.call("tk", "scaling", escala["ts0"] * escala["s"] / escala["s0"])
            except Exception:
                pass
        try:
            superior.configure(height=px(36))
            cinta.configure(height=px(44))
            riel_der.configure(width=px(44))
        except Exception:
            pass
        for d_ in Desliz.todas:
            try:
                d_.reescalar()
            except Exception:
                pass
        for f_ in (dibujar_superior, dibujar_cinta, dibujar_riel_der, dibujar_herr, redibujar_todo):
            try:
                f_()
            except Exception:
                pass
        if app["pagina"] == "organizar":
            org_dibujar(True)

    def revisar_monitor():
        T_ = ctk.ScalingTracker
        try:
            ahora = time.monotonic()
            for w_ in list(T_.window_widgets_dict):
                try:
                    if not w_.winfo_exists() or w_.state() == "iconic":
                        continue
                    nueva = T_.get_window_dpi_scaling(w_)
                except Exception:
                    continue
                if nueva == T_.window_dpi_scaling_dict.get(w_):
                    continue
                geo_ = w_.winfo_geometry()
                if escala["geo"].get(w_) != geo_ or _boton_apretado():  # todavia se esta moviendo
                    escala["geo"][w_] = geo_
                    escala["quieta"][w_] = ahora
                    continue
                if ahora - escala["quieta"].get(w_, ahora) >= 0.35:
                    ajustar_escala(w_, nueva)
                    escala["geo"].pop(w_, None)
        finally:
            raiz.after(200, revisar_monitor)
    raiz.after(1500, revisar_monitor)
    raiz.bind("<Map>", lambda e: raiz.after(60, redibujar_todo) if e.widget is raiz else None, add="+")
    # ---- v2.4: arrastrar PDF a la ventana (visor: se abren; Organizar: las opciones de «Unir»)
    def soltar_pdf(datos):
        try:
            items_ = raiz.tk.splitlist(datos)
        except Exception:
            items_ = [datos]
        rutas_ = [os.path.normpath(x) for x in items_ if os.path.isfile(x) and x.lower().endswith(".pdf")]
        if not rutas_:
            v_estado.set("Solo se pueden soltar archivos PDF.")
        else:
            raiz.after(30, lambda: abrir_soltados(rutas_))
        return "copy"

    def abrir_soltados(rutas_):
        try:
            raiz.lift()
            raiz.focus_force()
        except Exception:
            pass
        if app["pagina"] == "organizar":
            if org["preparando"]:
                v_estado.set("Esperá a que termine de preparar las páginas.")
                return
            if not org["orden"]:  # Organizar vacio: el primero se abre aca mismo y el resto se une
                if not abrir_pestana(rutas_[0], mostrar_visor=False):
                    return
                rutas_ = rutas_[1:]
                if not rutas_:
                    return
            org_dialogo(rutas_, True, lambda pos, prep: org_traer(rutas_, pos, prep, nuevo=False))
            return
        for r_ in rutas_:
            abrir_pestana(r_)

    def activar_soltar():
        try:
            from tkinterdnd2 import TkinterDnD, DND_FILES
            TkinterDnD._require(raiz)
        except Exception:
            return False  # sin tkdnd: todo lo demas funciona igual
        cmd_ = raiz.register(soltar_pdf)
        cmd_ok = raiz.register(lambda *_a: "copy")
        for w_ in (raiz, cuerpo, contenido, cv, cvm):
            try:
                raiz.tk.call("tkdnd::drop_target", "register", w_._w, DND_FILES)
                raiz.tk.call("bind", w_._w, "<<DropEnter>>", cmd_ok)
                raiz.tk.call("bind", w_._w, "<<DropPosition>>", cmd_ok)
                raiz.tk.call("bind", w_._w, "<<Drop>>", cmd_ + " %D")
            except Exception:
                pass
        return True

    app["soltar"] = activar_soltar()
    dibujar_pestanas()
    for a_ in sys.argv[1:]:  # PDF arrastrados sobre el .exe o «Abrir con»: una pestana cada uno
        if os.path.isfile(a_) and a_.lower().endswith(".pdf"):
            abrir_pestana(os.path.abspath(a_))
    mostrar_pagina("visor")
    for n_, b in botones_tema.items():
        b.configure(border_color=C["acento"] if n_ == V["apariencia"].get() else C["tarjeta"])
    refrescar_perfiles()
    refrescar()
    actualizar_ejemplo()
    raiz.after(150, revisar_modo)
    raiz.after(1500, vigilar_modo)
    raiz.after(120, procesar_eventos)
    raiz.after(60, recibir_dibujos)
    raiz.after(10, mostrar_ventana)
    auto_ = os.environ.get("PDFOL_AUTOPRUEBA")
    if auto_:  # prueba automatica (la usa GitHub antes de publicar): abre, recorre todo y cierra
        def _fallo(*a_):
            import traceback
            with open(os.environ.get("PDFOL_AUTOPRUEBA_LOG", "pdfol_autoprueba.log"), "a", encoding="utf-8") as f_:
                f_.write("".join(traceback.format_exception(*a_)))
            for p_ in mp.active_children():  # que no queden procesos de dibujo vivos
                try:
                    p_.terminate()
                except Exception:
                    pass
            os._exit(3)

        raiz.report_callback_exception = _fallo
        if os.name == "nt" and not app.get("soltar"):  # v2.6: que no falte lo de arrastrar al quitar archivos sobrantes
            _fallo(RuntimeError, RuntimeError("No se pudo activar arrastrar archivos (tkdnd)"), None)
        claves_ = ["organizar", "visor"] + [c_ for c_, *_ in ICONOS if c_ in EN_PANEL and c_ not in PROXIMAMENTE]
        pasos_ = [lambda: abrir_pestana(auto_) if os.path.isfile(auto_) else None]
        pasos_ += [lambda c_=c_: mostrar_pagina(c_) for c_ in claves_]
        pasos_ += [lambda: mostrar_pagina("visor"), lambda: alternar_resaltar(), lambda: alternar_resaltar(),
                   lambda: abrir_soltados([auto_]) if os.path.isfile(auto_) else None]
        prueba_ocr = {}

        def ocr_iniciar():  # v4.1: que el .exe traiga los idiomas del OCR y reconozca un escaneo
            import tempfile
            d_ = fitz.open()
            pg_ = d_.new_page(width=420, height=200)
            pg_.insert_text((30, 90), "PdFOL prueba OCR 2026", fontsize=26)
            png_ = pg_.get_pixmap(dpi=150).tobytes("png")
            e_ = fitz.open()
            pe_ = e_.new_page(width=420, height=200)
            pe_.insert_image(pe_.rect, stream=png_)
            prueba_ocr["ruta"] = os.path.join(tempfile.gettempdir(), "pdfol_prueba_ocr.pdf")
            e_.save(prueba_ocr["ruta"])
            if not _carpeta_tessdata():
                _fallo(RuntimeError, RuntimeError("Faltan los idiomas del OCR (tessdata)"), None)
            ocr_pedir(prueba_ocr["ruta"], 0, avisar=False, forzar=True)

        def ocr_revisar():
            r_ = ocr_de(prueba_ocr.get("ruta", ""), 0)
            txt_ = "".join(c_[5] for c_ in (r_ or {}).get("letras", []))
            if "OCR" not in txt_:
                _fallo(RuntimeError, RuntimeError(f"El OCR no reconocio el texto de prueba: {r_}"), None)
        pasos_ = [ocr_iniciar] + pasos_
        for n_, f_ in enumerate(pasos_):
            raiz.after(3000 + 700 * n_, f_)
        raiz.after(3000 + 700 * len(pasos_) + 1500, ocr_revisar)
        raiz.after(3000 + 700 * len(pasos_) + 2500, salir_del_todo)
    if not (os.environ.get("PDFOL_PRUEBA") or auto_):
        raiz.after(2500, buscar_actualizacion)  # al abrir: si no hay internet, no molesta
        raiz.after(1800, preguntar_abrir_siempre)
        raiz.after(3000, anotar_version_instalada)  # version instalada: ¿abrir siempre los PDF con PdFOL?
    if os.environ.get("PDFOL_PRUEBA"):  # solo para las pruebas automaticas
        globals()["_PRUEBA"] = locals()
    raiz.mainloop()



# =========================================================================
#  CONSOLA (opcional)
# =========================================================================
def modo_consola(argv):
    import argparse
    ap = argparse.ArgumentParser(prog=f"{NOMBRE}_{VERSION}", description="Aplanar, foliar y comprimir PDFs.")
    ap.add_argument("pdf")
    ap.add_argument("--aplanar", action="store_true")
    ap.add_argument("--foliar", action="store_true")
    ap.add_argument("--comprimir", choices=list(NIVELES), default=None)
    ap.add_argument("--dpi", type=int, default=DPI_DEFECTO)
    ap.add_argument("--nucleos", type=int, default=None)
    ap.add_argument("--umbral-kb", type=float, default=None)
    ap.add_argument("--paginas", default="")
    ap.add_argument("--excluir", default="")
    ap.add_argument("--sin-texto", action="store_true")
    ap.add_argument("--inicio", type=int, default=1)
    ap.add_argument("--digitos", type=int, default=4)
    ap.add_argument("--desde", type=int, default=1)
    ap.add_argument("--hasta", type=int, default=None)
    ap.add_argument("--con-total", action="store_true")
    ap.add_argument("--prefijo", default="Folio")
    ap.add_argument("--fuente", default="Special Elite (sello)")
    ap.add_argument("--tam", type=float, default=12)
    ap.add_argument("--negrita", action="store_true")
    ap.add_argument("--color", default="0,0,0")
    ap.add_argument("--posicion", default="Abajo derecha", choices=list(POSICIONES))
    ap.add_argument("--margen-h", type=float, default=10)
    ap.add_argument("--margen-v", type=float, default=10)
    a = ap.parse_args(argv)
    ruta = os.path.abspath(a.pdf)
    pes, scores = set(), None
    if a.aplanar:
        print(f"Analizando {ruta} ...")
        scores, umbral = analizar(ruta)
        if a.umbral_kb is not None:
            umbral = a.umbral_kb
        n = len(scores)
        pes = {i for i, s in enumerate(scores) if s >= umbral}
        pes |= parsear_paginas(a.paginas, n)
        pes -= parsear_paginas(a.excluir, n)
        print(f"Planos pesados: {len(pes)} de {n}")
    folio = None
    if a.foliar:
        folio = folio_por_defecto()
        folio.update(inicio=a.inicio, digitos=a.digitos, desde=a.desde, hasta=a.hasta, con_total=a.con_total,
                     prefijo=a.prefijo, fuente=a.fuente, tam=a.tam, negrita=a.negrita,
                     color=tuple(int(x) for x in a.color.split(",")), posicion=a.posicion,
                     margen_h_mm=a.margen_h, margen_v_mm=a.margen_v)
    r = procesar(ruta, pes, dpi=a.dpi, nucleos=a.nucleos, texto=not a.sin_texto, folio=folio,
                 compresion=a.comprimir, scores=scores,
                 progreso=lambda h, t, eta: print(f"  Plano {h}/{t} - faltan {fmt_tiempo(eta)}     ", end="\r"),
                 estado=lambda m: print("\n" + m, end=""))
    print(f"\nListo en {fmt_tiempo(r['segundos'])}: {r['salida']}")
    print(f"Tamaño: {r['mb_entrada']:.1f} MB -> {r['mb_salida']:.1f} MB")


if __name__ == "__main__":
    mp.freeze_support()
    try:  # igual que en Windows: procesos nuevos (no copias), en cualquier sistema
        mp.set_start_method("spawn")
    except RuntimeError:
        pass
    args = sys.argv[1:]
    if "--pdfol-crear-splash" in args:  # v3.0: lo usa la compilacion (imagen de inicio del .exe)
        crear_imagen_inicio(args[args.index("--pdfol-crear-splash") + 1])
    elif any(x.startswith("--") for x in args):
        modo_consola(args)
    else:
        iniciar_interfaz()
