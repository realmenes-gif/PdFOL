package com.meneses999.pdfol;

import android.content.ContentProvider;
import android.content.ContentValues;
import android.database.Cursor;
import android.database.MatrixCursor;
import android.net.Uri;
import android.os.ParcelFileDescriptor;
import android.provider.OpenableColumns;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;

/** Entrega a otras apps el PDF que se comparte (solo lectura, solo la carpeta «compartir»). */
public class Archivos extends ContentProvider {
    static final String AUTORIDAD = "com.meneses999.pdfol.archivos";

    File archivo(Uri u) throws FileNotFoundException {
        if (u.getPathSegments().size() != 2 || !"compartir".equals(u.getPathSegments().get(0))) throw new FileNotFoundException();
        File dir = new File(getContext().getCacheDir(), "compartir");
        File f = new File(dir, u.getPathSegments().get(1));
        try {
            if (!f.getCanonicalPath().startsWith(dir.getCanonicalPath() + File.separator) || !f.isFile()) throw new FileNotFoundException();
        } catch (IOException e) {
            throw new FileNotFoundException();
        }
        return f;
    }

    @Override public boolean onCreate() { return true; }

    @Override
    public Cursor query(Uri uri, String[] proy, String sel, String[] args, String orden) {
        MatrixCursor c = new MatrixCursor(new String[]{OpenableColumns.DISPLAY_NAME, OpenableColumns.SIZE});
        try {
            File f = archivo(uri);
            c.addRow(new Object[]{f.getName(), f.length()});
        } catch (FileNotFoundException e) { /* vacio */ }
        return c;
    }

    @Override public String getType(Uri uri) { return "application/pdf"; }

    @Override
    public ParcelFileDescriptor openFile(Uri uri, String modo) throws FileNotFoundException {
        return ParcelFileDescriptor.open(archivo(uri), ParcelFileDescriptor.MODE_READ_ONLY);
    }

    @Override public Uri insert(Uri uri, ContentValues v) { return null; }
    @Override public int delete(Uri uri, String s, String[] a) { return 0; }
    @Override public int update(Uri uri, ContentValues v, String s, String[] a) { return 0; }
}
