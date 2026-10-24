package com.meneses999.pdfol;

import android.app.Activity;
import android.content.ActivityNotFoundException;
import android.content.ContentResolver;
import android.content.Intent;
import android.content.UriPermission;
import android.content.res.Configuration;
import android.database.Cursor;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.ColorFilter;
import android.graphics.Insets;
import android.graphics.Paint;
import android.graphics.PixelFormat;
import android.graphics.drawable.Drawable;
import android.net.Uri;
import android.os.Bundle;
import android.provider.OpenableColumns;
import android.util.Base64;
import android.view.View;
import android.view.WindowInsets;
import android.view.WindowInsetsController;
import android.webkit.JavascriptInterface;
import android.webkit.WebChromeClient;
import android.webkit.WebResourceRequest;
import android.webkit.WebResourceResponse;
import android.webkit.WebSettings;
import android.webkit.WebView;
import android.webkit.WebViewClient;
import android.widget.FrameLayout;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * PdFOL para Android: la interfaz es una pagina web local (assets/www) con pdf.js.
 * Esta actividad solo muestra esa pagina, le pasa los PDF que se abren y guarda lo que ella devuelve.
 */
public class MainActivity extends Activity {

    static final String HOST = "appassets.androidplatform.net";
    static final String INICIO = "https://" + HOST + "/www/index.html";
    static final int REQ_ABRIR = 1, REQ_COPIA = 2;

    WebView web;
    FrameLayout raiz;
    final FondoBarras fondo = new FondoBarras();
    final Map<String, Doc> docs = new HashMap<>();
    final List<Doc> pendientes = new ArrayList<>();
    final ExecutorService hilo = Executors.newSingleThreadExecutor();
    volatile boolean paginaLista = false;
    String copiaToken = null, copiaNombre = null;

    static class Doc {
        String id, nombre;
        Uri uri;
        long tam;
        boolean persistente;

        JSONObject json() throws JSONException {
            return new JSONObject().put("id", id).put("nombre", nombre).put("uri", uri.toString())
                    .put("tam", tam).put("persistente", persistente);
        }
    }

    // ------------------------------------------------------------------ ventana
    @Override
    protected void onCreate(Bundle b) {
        super.onCreate(b);
        getWindow().setDecorFitsSystemWindows(false);
        raiz = new FrameLayout(this);
        raiz.setBackground(fondo);
        web = new WebView(this);
        raiz.addView(web, new FrameLayout.LayoutParams(-1, -1));
        setContentView(raiz);
        // la pagina queda entre la barra de estado y la de navegacion (y sube con el teclado)
        raiz.setOnApplyWindowInsetsListener((v, ins) -> {
            Insets s = ins.getInsets(WindowInsets.Type.systemBars() | WindowInsets.Type.displayCutout());
            Insets t = ins.getInsets(WindowInsets.Type.ime());
            v.setPadding(s.left, s.top, s.right, Math.max(s.bottom, t.bottom));
            fondo.alto = s.top;
            fondo.invalidateSelf();
            return WindowInsets.CONSUMED;
        });
        boolean oscuro = modoOscuroSistema();
        int c = oscuro ? 0xFF1A1E24 : 0xFFF6F8FB;
        fondo.arriba = oscuro ? 0xFF272D36 : 0xFFEEF2F7;
        fondo.abajo = c;
        web.setBackgroundColor(c);
        iconosBarras(oscuro);

        WebSettings w = web.getSettings();
        w.setJavaScriptEnabled(true);
        w.setDomStorageEnabled(true);
        w.setAllowFileAccess(false);
        w.setAllowContentAccess(false);
        w.setSupportZoom(false);
        w.setBuiltInZoomControls(false);
        w.setTextZoom(100);
        w.setMixedContentMode(WebSettings.MIXED_CONTENT_NEVER_ALLOW);
        web.setOverScrollMode(View.OVER_SCROLL_NEVER);
        web.addJavascriptInterface(new Puente(), "PdfolAndroid");
        web.setWebChromeClient(new WebChromeClient());
        web.setWebViewClient(new WebViewClient() {
            @Override
            public WebResourceResponse shouldInterceptRequest(WebView view, WebResourceRequest req) {
                return servir(req.getUrl());
            }

            @Override
            public boolean shouldOverrideUrlLoading(WebView view, WebResourceRequest req) {
                Uri u = req.getUrl();
                if (HOST.equals(u.getHost())) return false;
                abrirFuera(u); // enlaces de los PDF: en el navegador
                return true;
            }
        });
        manejarIntent(getIntent());
        web.loadUrl(INICIO);
    }

    boolean modoOscuroSistema() {
        return (getResources().getConfiguration().uiMode & Configuration.UI_MODE_NIGHT_MASK)
                == Configuration.UI_MODE_NIGHT_YES;
    }

    void iconosBarras(boolean oscuro) {
        WindowInsetsController c = getWindow().getInsetsController();
        if (c == null) return;
        int claras = WindowInsetsController.APPEARANCE_LIGHT_STATUS_BARS
                | WindowInsetsController.APPEARANCE_LIGHT_NAVIGATION_BARS;
        c.setSystemBarsAppearance(oscuro ? 0 : claras, claras);
    }

    @Override
    public void onConfigurationChanged(Configuration n) {
        super.onConfigurationChanged(n);
        js("window.pdfolTemaSistema && pdfolTemaSistema()");
    }

    @Override
    protected void onNewIntent(Intent i) {
        super.onNewIntent(i);
        manejarIntent(i);
    }

    @Override
    @SuppressWarnings("deprecation")
    public void onBackPressed() {
        web.evaluateJavascript("window.pdfolAtras ? pdfolAtras() : false", v -> {
            if (!"true".equals(v)) finish();
        });
    }

    @Override
    protected void onDestroy() {
        hilo.shutdown();
        if (web != null) web.destroy();
        super.onDestroy();
    }

    void js(String codigo) {
        runOnUiThread(() -> web.evaluateJavascript(codigo, null));
    }

    void abrirFuera(Uri u) {
        String s = u.getScheme();
        if (!"https".equals(s) && !"http".equals(s) && !"mailto".equals(s)) return;
        try {
            startActivity(new Intent(Intent.ACTION_VIEW, u));
        } catch (ActivityNotFoundException e) { /* sin navegador */ }
    }

    // ------------------------------------------------------------------ archivos de la pagina y PDF abiertos
    WebResourceResponse servir(Uri u) {
        if (!HOST.equals(u.getHost()) || u.getPath() == null) return null;
        String p = u.getPath();
        Map<String, String> cab = new HashMap<>();
        cab.put("Cache-Control", "no-cache");
        try {
            if (p.startsWith("/www/") && !p.contains("..")) {
                String a = p.substring(1);
                return new WebResourceResponse(tipo(a), null, 200, "OK", cab, getAssets().open(a));
            }
            if (p.startsWith("/doc/")) {
                Doc d;
                synchronized (docs) { d = docs.get(u.getLastPathSegment()); }
                if (d != null) {
                    InputStream in = getContentResolver().openInputStream(d.uri);
                    if (d.tam > 0) cab.put("Content-Length", String.valueOf(d.tam));
                    return new WebResourceResponse("application/pdf", null, 200, "OK", cab, in);
                }
            }
        } catch (Exception e) { /* no existe o sin permiso */ }
        return new WebResourceResponse("text/plain", "utf-8", 404, "Not Found", cab, null);
    }

    static String tipo(String a) {
        if (a.endsWith(".html")) return "text/html";
        if (a.endsWith(".js") || a.endsWith(".mjs")) return "text/javascript";
        if (a.endsWith(".css")) return "text/css";
        if (a.endsWith(".png")) return "image/png";
        if (a.endsWith(".svg")) return "image/svg+xml";
        if (a.endsWith(".wasm")) return "application/wasm";
        if (a.endsWith(".json")) return "application/json";
        return "application/octet-stream";
    }

    Doc registrar(Uri uri, boolean persistente) {
        Doc d = new Doc();
        d.id = UUID.randomUUID().toString().substring(0, 12);
        d.uri = uri;
        d.persistente = persistente;
        d.nombre = "documento.pdf";
        try (Cursor c = getContentResolver().query(uri, null, null, null, null)) {
            if (c != null && c.moveToFirst()) {
                int n = c.getColumnIndex(OpenableColumns.DISPLAY_NAME), t = c.getColumnIndex(OpenableColumns.SIZE);
                if (n >= 0 && c.getString(n) != null) d.nombre = c.getString(n);
                if (t >= 0 && !c.isNull(t)) d.tam = c.getLong(t);
            }
        } catch (Exception e) { /* algunos proveedores no responden */ }
        if (d.nombre.equals("documento.pdf") && uri.getLastPathSegment() != null) {
            String s = uri.getLastPathSegment();
            if (s.toLowerCase().endsWith(".pdf")) d.nombre = s.substring(s.lastIndexOf('/') + 1);
        }
        synchronized (docs) { docs.put(d.id, d); }
        return d;
    }

    @SuppressWarnings("deprecation")
    void manejarIntent(Intent i) {
        if (i == null) return;
        List<Uri> uris = new ArrayList<>();
        String a = i.getAction();
        if (Intent.ACTION_VIEW.equals(a) && i.getData() != null) {
            uris.add(i.getData());
        } else if (Intent.ACTION_SEND.equals(a)) {
            Uri u = i.getParcelableExtra(Intent.EXTRA_STREAM);
            if (u != null) uris.add(u);
        } else if (Intent.ACTION_SEND_MULTIPLE.equals(a)) {
            ArrayList<Uri> l = i.getParcelableArrayListExtra(Intent.EXTRA_STREAM);
            if (l != null) uris.addAll(l);
        }
        if (uris.isEmpty()) return;
        hilo.execute(() -> {
            synchronized (pendientes) {
                for (Uri u : uris) pendientes.add(registrar(u, false));
            }
            if (paginaLista) js("window.pdfolNativo && pdfolNativo.nuevos()");
        });
    }

    @Override
    protected void onActivityResult(int req, int res, Intent datos) {
        super.onActivityResult(req, res, datos);
        if (req == REQ_ABRIR) {
            if (res != RESULT_OK || datos == null) return;
            List<Uri> uris = new ArrayList<>();
            if (datos.getClipData() != null) {
                for (int k = 0; k < datos.getClipData().getItemCount(); k++) uris.add(datos.getClipData().getItemAt(k).getUri());
            } else if (datos.getData() != null) uris.add(datos.getData());
            hilo.execute(() -> {
                synchronized (pendientes) {
                    for (Uri u : uris) pendientes.add(registrar(u, guardarPermiso(u)));
                }
                js("window.pdfolNativo && pdfolNativo.nuevos()");
            });
        } else if (req == REQ_COPIA) {
            String token = copiaToken;
            copiaToken = null;
            if (token == null) return;
            if (res != RESULT_OK || datos == null || datos.getData() == null) {
                resultado(token, false, "cancelado", null);
                return;
            }
            Uri destino = datos.getData();
            hilo.execute(() -> {
                File f = archivoEscritura(token);
                try {
                    copiar(f, destino);
                    Doc d = registrar(destino, guardarPermiso(destino));
                    resultado(token, true, "", d.json());
                } catch (Exception e) {
                    resultado(token, false, "No se pudo guardar la copia.", null);
                } finally {
                    f.delete();
                }
            });
        }
    }

    boolean guardarPermiso(Uri u) {
        ContentResolver r = getContentResolver();
        try {
            r.takePersistableUriPermission(u, Intent.FLAG_GRANT_READ_URI_PERMISSION | Intent.FLAG_GRANT_WRITE_URI_PERMISSION);
            return true;
        } catch (SecurityException e) {
            try {
                r.takePersistableUriPermission(u, Intent.FLAG_GRANT_READ_URI_PERMISSION);
                return true;
            } catch (SecurityException e2) {
                return false;
            }
        }
    }

    // ------------------------------------------------------------------ escritura (guardar, copia, compartir)
    File archivoEscritura(String token) {
        File dir = new File(getCacheDir(), "escritura");
        dir.mkdirs();
        return new File(dir, token.replaceAll("[^a-zA-Z0-9]", "") + ".pdf");
    }

    void copiar(File f, Uri destino) throws IOException {
        try (InputStream in = new FileInputStream(f);
             OutputStream out = getContentResolver().openOutputStream(destino, "wt")) {
            if (out == null) throw new IOException("sin salida");
            byte[] buf = new byte[256 * 1024];
            int n;
            while ((n = in.read(buf)) > 0) out.write(buf, 0, n);
        }
    }

    void resultado(String token, boolean ok, String msg, JSONObject extra) {
        js("pdfolNativo.escrito(" + JSONObject.quote(token) + "," + ok + "," + JSONObject.quote(msg) + ","
                + (extra == null ? "null" : JSONObject.quote(extra.toString())) + ")");
    }

    static String nombreSeguro(String n) {
        String s = n == null ? "" : n.replaceAll("[\\\\/:*?\"<>|\\p{Cntrl}]", "_").trim();
        if (s.isEmpty()) s = "documento.pdf";
        if (!s.toLowerCase().endsWith(".pdf")) s += ".pdf";
        return s;
    }

    void terminar(String token, String modo, String idDoc, String nombre) {
        File f = archivoEscritura(token);
        if ("original".equals(modo)) {
            Doc d;
            synchronized (docs) { d = docs.get(idDoc); }
            if (d == null) { resultado(token, false, "sinpermiso", null); return; }
            try {
                copiar(f, d.uri);
                File g = new File(f.getPath());
                d.tam = g.length();
                resultado(token, true, "", d.json());
            } catch (Exception e) {
                resultado(token, false, "sinpermiso", null);
            } finally {
                f.delete();
            }
        } else if ("copia".equals(modo)) {
            copiaToken = token;
            copiaNombre = nombreSeguro(nombre);
            runOnUiThread(() -> {
                Intent i = new Intent(Intent.ACTION_CREATE_DOCUMENT);
                i.addCategory(Intent.CATEGORY_OPENABLE);
                i.setType("application/pdf");
                i.putExtra(Intent.EXTRA_TITLE, copiaNombre);
                try {
                    startActivityForResult(i, REQ_COPIA);
                } catch (ActivityNotFoundException e) {
                    copiaToken = null;
                    resultado(token, false, "No hay dónde guardar la copia.", null);
                }
            });
        } else if ("compartir".equals(modo)) {
            File dir = new File(getCacheDir(), "compartir");
            File[] viejos = dir.listFiles();
            if (viejos != null) for (File v : viejos) v.delete();
            dir.mkdirs();
            File dest = new File(dir, nombreSeguro(nombre));
            if (!f.renameTo(dest)) { resultado(token, false, "No se pudo compartir.", null); return; }
            Uri u = new Uri.Builder().scheme("content").authority(Archivos.AUTORIDAD)
                    .appendPath("compartir").appendPath(dest.getName()).build();
            runOnUiThread(() -> {
                Intent i = new Intent(Intent.ACTION_SEND);
                i.setType("application/pdf");
                i.putExtra(Intent.EXTRA_STREAM, u);
                i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION);
                try {
                    startActivity(Intent.createChooser(i, "Compartir PDF"));
                    resultado(token, true, "", null);
                } catch (ActivityNotFoundException e) {
                    resultado(token, false, "No hay apps para compartir.", null);
                }
            });
        }
    }

    // ------------------------------------------------------------------ puente con la pagina
    class Puente {
        @JavascriptInterface
        public String pendientes() {
            JSONArray a = new JSONArray();
            synchronized (pendientes) {
                for (Doc d : pendientes) {
                    try { a.put(d.json()); } catch (JSONException e) { /* nada */ }
                }
                pendientes.clear();
            }
            return a.toString();
        }

        @JavascriptInterface
        public void listo() {
            paginaLista = true;
            boolean hay;
            synchronized (pendientes) { hay = !pendientes.isEmpty(); }
            if (hay) js("window.pdfolNativo && pdfolNativo.nuevos()");
        }

        @JavascriptInterface
        public void elegirArchivo() {
            runOnUiThread(() -> {
                Intent i = new Intent(Intent.ACTION_OPEN_DOCUMENT);
                i.addCategory(Intent.CATEGORY_OPENABLE);
                i.setType("application/pdf");
                i.putExtra(Intent.EXTRA_ALLOW_MULTIPLE, true);
                i.addFlags(Intent.FLAG_GRANT_READ_URI_PERMISSION | Intent.FLAG_GRANT_WRITE_URI_PERMISSION
                        | Intent.FLAG_GRANT_PERSISTABLE_URI_PERMISSION);
                try {
                    startActivityForResult(i, REQ_ABRIR);
                } catch (ActivityNotFoundException e) { /* sin selector */ }
            });
        }

        @JavascriptInterface
        public String reabrir(String uri) {
            Uri u = Uri.parse(uri);
            for (UriPermission p : getContentResolver().getPersistedUriPermissions()) {
                if (p.getUri().equals(u) && p.isReadPermission()) {
                    try (InputStream in = getContentResolver().openInputStream(u)) {
                        if (in == null) return "";
                    } catch (Exception e) {
                        return "";
                    }
                    try { return registrar(u, true).json().toString(); } catch (JSONException e) { return ""; }
                }
            }
            return "";
        }

        @JavascriptInterface
        public String nuevaEscritura() {
            String t = UUID.randomUUID().toString().replace("-", "");
            archivoEscritura(t).delete();
            return t;
        }

        @JavascriptInterface
        public boolean escribirParte(String token, String b64) {
            try (FileOutputStream o = new FileOutputStream(archivoEscritura(token), true)) {
                o.write(Base64.decode(b64, Base64.DEFAULT));
                return true;
            } catch (Exception e) {
                return false;
            }
        }

        @JavascriptInterface
        public void terminarEscritura(String token, String modo, String idDoc, String nombre) {
            hilo.execute(() -> terminar(token, modo, idDoc, nombre));
        }

        @JavascriptInterface
        public String version() {
            try {
                return getPackageManager().getPackageInfo(getPackageName(), 0).versionName;
            } catch (Exception e) {
                return "";
            }
        }

        @JavascriptInterface
        public boolean modoOscuro() {
            return modoOscuroSistema();
        }

        @JavascriptInterface
        public void colorBarras(String arriba, String abajo, boolean oscuro) {
            runOnUiThread(() -> {
                try {
                    fondo.arriba = Color.parseColor(arriba);
                    fondo.abajo = Color.parseColor(abajo);
                    web.setBackgroundColor(fondo.abajo);
                    fondo.invalidateSelf();
                    iconosBarras(oscuro);
                } catch (Exception e) { /* color invalido */ }
            });
        }

        @JavascriptInterface
        public void abrirUrl(String url) {
            if (url != null && url.startsWith("https://")) runOnUiThread(() -> abrirFuera(Uri.parse(url)));
        }
    }

    // fondo detras de las barras del sistema: arriba el color de la barra de PdFOL, abajo el del fondo
    static class FondoBarras extends Drawable {
        int arriba = 0xFFEEF2F7, abajo = 0xFFF6F8FB, alto = 0;
        final Paint p = new Paint();

        @Override
        public void draw(Canvas c) {
            p.setColor(abajo);
            c.drawRect(getBounds(), p);
            p.setColor(arriba);
            c.drawRect(0, 0, getBounds().width(), alto, p);
        }

        @Override public void setAlpha(int a) { }
        @Override public void setColorFilter(ColorFilter f) { }
        @Override public int getOpacity() { return PixelFormat.OPAQUE; }
    }
}
