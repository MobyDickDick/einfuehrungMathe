import ast
import numpy as np
import matplotlib.pyplot as plt
from matplotlib import cm
from matplotlib.widgets import TextBox, Button

# ---------------------------
# Kompaktifizierung R -> (-1,1), robust bei inf/overflow
# ---------------------------
def s(u):
    u = np.asarray(u, dtype=float)
    with np.errstate(all="ignore"):
        out = u / np.sqrt(1.0 + u*u)
    out = np.where(np.isinf(u), np.sign(u), out)
    return out

def s_inv(t):
    t = np.asarray(t, dtype=float)
    with np.errstate(all="ignore"):
        return t / np.sqrt(1.0 - t*t)

def s_prime(u):
    u = np.asarray(u, dtype=float)
    with np.errstate(all="ignore"):
        return 1.0 / np.power(1.0 + u*u, 1.5)

# ---------------------------
# Sichere (eingeschränkte) Formel-Auswertung
# ---------------------------
_ALLOWED_FUNCS = {
    "sin": np.sin, "cos": np.cos, "tan": np.tan,
    "arcsin": np.arcsin, "arccos": np.arccos, "arctan": np.arctan,
    "sinh": np.sinh, "cosh": np.cosh, "tanh": np.tanh,
    "exp": np.exp, "log": np.log, "log10": np.log10,
    "sqrt": np.sqrt, "abs": np.abs, "sign": np.sign,
    "floor": np.floor, "ceil": np.ceil,
    "maximum": np.maximum, "minimum": np.minimum,
    "where": np.where,
    "sinc": lambda x: np.where(np.asarray(x) == 0.0, 1.0, np.sin(x) / x),
}
_ALLOWED_NAMES = {"pi": np.pi, "e": np.e, "np": np, **_ALLOWED_FUNCS}

_ALLOWED_NODES = (
    ast.Expression,
    ast.BinOp, ast.UnaryOp,
    ast.Add, ast.Sub, ast.Mult, ast.Div, ast.Pow, ast.Mod,
    ast.USub, ast.UAdd,
    ast.Call,
    ast.Name,
    ast.Constant,
    ast.Load,
    ast.Attribute,
)

def _normalize_expr(expr: str) -> str:
    expr = expr.strip()
    if "=" in expr:
        expr = expr.split("=", 1)[1].strip()
    expr = expr.replace("^", "**")
    return expr

def _validate_ast(node: ast.AST):
    for n in ast.walk(node):
        if not isinstance(n, _ALLOWED_NODES):
            raise ValueError(f"Nicht erlaubter Ausdrucksteil: {type(n).__name__}")

        if isinstance(n, ast.Name):
            if n.id not in _ALLOWED_NAMES and n.id != "x":
                raise ValueError(f"Name nicht erlaubt: {n.id}")

        if isinstance(n, ast.Attribute):
            if not (isinstance(n.value, ast.Name) and n.value.id == "np"):
                raise ValueError("Nur Attribute der Form np.<...> sind erlaubt.")

        if isinstance(n, ast.Call):
            fn = n.func
            if isinstance(fn, ast.Name):
                if fn.id not in _ALLOWED_FUNCS:
                    raise ValueError(f"Funktion nicht erlaubt: {fn.id}")
            elif isinstance(fn, ast.Attribute):
                if not (isinstance(fn.value, ast.Name) and fn.value.id == "np"):
                    raise ValueError("Nur Aufrufe der Form np.<func>(...) sind erlaubt.")
                if fn.attr not in dir(np):
                    raise ValueError(f"np.{fn.attr} existiert nicht.")
            else:
                raise ValueError("Nicht erlaubter Funktionsaufruf.")

def make_user_function(expr: str):
    expr = _normalize_expr(expr)
    node = ast.parse(expr, mode="eval")
    _validate_ast(node)
    code = compile(node, "<user_function>", "eval")

    def f(x):
        env = dict(_ALLOWED_NAMES)
        env["x"] = x
        return eval(code, {"__builtins__": {}}, env)

    return f, expr

# ---------------------------
# f(x0) robust: direkt oder Grenzwert-Schätzung
# ---------------------------
def eval_at_or_limit(f, x0, n=60):
    with np.errstate(all="ignore"):
        try:
            v = f(np.array([x0], dtype=float))[0]
        except Exception:
            v = np.nan

    if np.isfinite(v):
        return float(v), False

    base = max(1.0, abs(x0))
    eps_list = np.logspace(-2, -14, n) * base
    vals = []

    with np.errstate(all="ignore"):
        for eps in eps_list:
            for xx in (x0 + eps, x0 - eps):
                try:
                    vv = f(np.array([xx], dtype=float))[0]
                    if np.isfinite(vv):
                        vals.append(float(vv))
                except Exception:
                    pass

    if len(vals) < 6:
        raise ValueError("f(x0) nicht auswertbar und kein stabiler Grenzwert erkennbar.")

    tail = vals[-min(20, len(vals)):]
    return float(np.median(tail)), True

# ---------------------------
# 3D-Surface: z = x/y in kompaktifizierten Koordinaten
# ---------------------------
def build_surface(ax, N=180, eps=1e-3, gap=0.02, alpha=0.35):
    t = np.linspace(-1 + eps, 1 - eps, N)
    u_pos = np.linspace(gap, 1 - eps, N // 2)
    u_neg = np.linspace(-1 + eps, -gap, N // 2)

    def plot_sheet(u_vals):
        T, U = np.meshgrid(t, u_vals)
        X = s_inv(T)
        Y = s_inv(U)
        Z = s(X / Y)
        return ax.plot_surface(
            T, U, Z,
            cmap=cm.coolwarm,
            linewidth=0,
            antialiased=True,
            alpha=alpha,
            shade=False,
        )

    return plot_sheet(u_pos), plot_sheet(u_neg)

def choose_x_range(x0):
    R = max(5.0, 2.0 * abs(x0) + 1.0)
    R = min(R, 50.0)
    return x0 - R, x0 + R

def inv_label(v):
    if abs(v) >= 1.0:
        return "∞"
    return f"{(v / np.sqrt(1 - v*v)):.2g}"

def should_compactify_y(yvals, threshold=1e3):
    y = np.asarray(yvals, dtype=float)
    y = y[np.isfinite(y)]
    if y.size < 20:
        return True
    lo, hi = np.percentile(y, [2, 98])
    span = hi - lo
    mag = max(abs(lo), abs(hi), 1.0)
    return (mag > threshold) or (span > 2 * threshold)

# ---------------------------
# Hauptprogramm
# ---------------------------
def main():
    plt.close("all")
    fig = plt.figure(figsize=(12, 7))

    # WICHTIG: mehr Platz unten, damit Statuszeile + Buttons Platz haben
    gs = fig.add_gridspec(
        1, 2,
        width_ratios=[1.35, 1.0],
        left=0.05, right=0.98,
        bottom=0.22,   # <-- vorher 0.08; jetzt deutlich mehr
        top=0.88,
        wspace=0.25
    )
    ax3d = fig.add_subplot(gs[0, 0], projection="3d")
    ax2d = fig.add_subplot(gs[0, 1])

    # 3D surface
    build_surface(ax3d, N=180, eps=1e-3, gap=0.02, alpha=0.35)

    ax3d.set_xlim(-1, 1)
    ax3d.set_ylim(-1, 1)
    ax3d.set_zlim(-1, 1)
    ax3d.set_box_aspect((1, 1, 1))
    ax3d.set_xlabel("s(x)")
    ax3d.set_ylabel("s(y)")
    ax3d.set_zlabel("s(z)")
    ax3d.set_title("Kompaktifizierte Fläche z = x/y und Differenzenquotient-Kurve")

    ticks = np.array([-0.9, -0.6, -0.3, 0.0, 0.3, 0.6, 0.9])
    ticklabels = [inv_label(v) for v in ticks]
    ax3d.set_xticks(ticks); ax3d.set_xticklabels(ticklabels)
    ax3d.set_yticks(ticks); ax3d.set_yticklabels(ticklabels)
    ax3d.set_zticks(ticks); ax3d.set_zticklabels(ticklabels)

    # 3D Kurve (Outline + Linie + Punkte)
    line3d_bg, = ax3d.plot([], [], [], color="black", linewidth=6, alpha=0.9)
    line3d, = ax3d.plot([], [], [], color="red", linewidth=3, alpha=1.0)
    curve_pts = ax3d.scatter([], [], [], color="red", s=10, depthshade=False)
    marker3d = ax3d.scatter([], [], [], color="red", s=55, depthshade=False)

    # Start-View (für Reset)
    start_elev, start_azim, start_dist = 22.0, -55.0, 9.0
    ax3d.view_init(elev=start_elev, azim=start_azim)
    ax3d.dist = start_dist

    # 2D plot
    ax2d.grid(True)
    f_line2d, = ax2d.plot([], [], linewidth=2)
    tan_line2d, = ax2d.plot([], [], linewidth=2, linestyle="--")
    pt2d = ax2d.scatter([], [], s=40, zorder=3)

    # ---------------------------
    # Statusleiste (eigene Achse), damit nichts überdeckt wird
    # ---------------------------
    status_ax = fig.add_axes([0.05, 0.13, 0.93, 0.06])  # oberhalb der Buttonzeile
    status_ax.axis("off")
    status_text = status_ax.text(0.0, 0.5, "", va="center", ha="left", fontsize=10)

    # ---------------------------
    # Eingabefelder
    # ---------------------------
    axbox_f = plt.axes([0.12, 0.92, 0.62, 0.05])
    axbox_x0 = plt.axes([0.78, 0.92, 0.10, 0.05])
    axbtn_update = plt.axes([0.90, 0.92, 0.08, 0.05])

    tb_f = TextBox(axbox_f, "f(x) = ", initial="sin(x)/x")
    tb_x0 = TextBox(axbox_x0, "x0 = ", initial="5")
    btn_update = Button(axbtn_update, "Update")

    # ---------------------------
    # 3D Navigation Buttons (unterhalb der Statusleiste)
    # ---------------------------
    nav_y = 0.06
    nav_w = 0.05
    nav_h = 0.06
    nav_x0 = 0.12

    ax_left  = plt.axes([nav_x0 + 0.00, nav_y, nav_w, nav_h])
    ax_right = plt.axes([nav_x0 + 0.055, nav_y, nav_w, nav_h])
    ax_up    = plt.axes([nav_x0 + 0.110, nav_y, nav_w, nav_h])
    ax_down  = plt.axes([nav_x0 + 0.165, nav_y, nav_w, nav_h])
    ax_zoom_in  = plt.axes([nav_x0 + 0.220, nav_y, nav_w, nav_h])
    ax_zoom_out = plt.axes([nav_x0 + 0.275, nav_y, nav_w, nav_h])
    ax_reset = plt.axes([nav_x0 + 0.335, nav_y, 0.08, nav_h])

    btn_left  = Button(ax_left,  "←")
    btn_right = Button(ax_right, "→")
    btn_up    = Button(ax_up,    "↑")
    btn_down  = Button(ax_down,  "↓")
    btn_zoom_in  = Button(ax_zoom_in,  "+")
    btn_zoom_out = Button(ax_zoom_out, "-")
    btn_reset = Button(ax_reset, "Reset")

    def redraw3d():
        fig.canvas.draw_idle()

    def rotate(da=0.0, de=0.0):
        az = ax3d.azim + da
        el = ax3d.elev + de
        el = max(-89.0, min(89.0, el))
        ax3d.view_init(elev=el, azim=az)
        redraw3d()

    def zoom(factor):
        d = getattr(ax3d, "dist", 10.0)
        d = d * factor
        d = max(2.0, min(30.0, d))
        ax3d.dist = d
        redraw3d()

    def reset_view(_=None):
        ax3d.view_init(elev=start_elev, azim=start_azim)
        ax3d.dist = start_dist
        redraw3d()

    btn_left.on_clicked(lambda _: rotate(da=-8.0))
    btn_right.on_clicked(lambda _: rotate(da=+8.0))
    btn_up.on_clicked(lambda _: rotate(de=+6.0))
    btn_down.on_clicked(lambda _: rotate(de=-6.0))
    btn_zoom_in.on_clicked(lambda _: zoom(0.85))
    btn_zoom_out.on_clicked(lambda _: zoom(1.18))
    btn_reset.on_clicked(reset_view)

    # ---------------------------
    # Update-Funktion
    # ---------------------------
    def update(_=None):
        nonlocal pt2d

        expr_in = tb_f.text
        x0_in = tb_x0.text.strip().replace(",", ".")
        try:
            x0 = float(x0_in)
        except ValueError:
            status_text.set_text("Fehler: x0 ist keine Zahl.")
            fig.canvas.draw_idle()
            return

        try:
            f, expr_norm = make_user_function(expr_in)
        except Exception as e:
            status_text.set_text(f"Fehler in f(x): {e}")
            fig.canvas.draw_idle()
            return

        # h sampling (ohne 0)
        hmin, hmax = 1e-6, 1e1
        hs_pos = np.logspace(np.log10(hmin), np.log10(hmax), 600)
        hs = np.concatenate((-hs_pos[::-1], hs_pos))

        # f(x0)
        try:
            f0, used_limit = eval_at_or_limit(f, x0)
        except Exception as e:
            status_text.set_text(f"Fehler: f(x0) nicht bestimmbar: {e}")
            fig.canvas.draw_idle()
            return

        # 3D Kurve
        try:
            with np.errstate(all="ignore"):
                fx = f(x0 + hs)
            delta = fx - f0
            dq = delta / hs
        except Exception as e:
            status_text.set_text(f"Auswertefehler: {e}")
            fig.canvas.draw_idle()
            return

        Xc, Yc, Zc = s(delta), s(hs), s(dq)
        mask = np.isfinite(Xc) & np.isfinite(Yc) & np.isfinite(Zc)
        Xc, Yc, Zc = Xc[mask], Yc[mask], Zc[mask]

        line3d_bg.set_data(Xc, Yc)
        line3d_bg.set_3d_properties(Zc)
        line3d.set_data(Xc, Yc)
        line3d.set_3d_properties(Zc)

        if Xc.size > 0:
            step = max(1, Xc.size // 250)
            curve_pts._offsets3d = (Xc[::step], Yc[::step], Zc[::step])
        else:
            curve_pts._offsets3d = ([], [], [])

        # Derivat approx
        d_approx = np.nan
        try:
            h0 = 1e-6
            with np.errstate(all="ignore"):
                d_approx = (f(x0 + h0) - f(x0 - h0)) / (2*h0)
        except Exception:
            pass

        if np.isfinite(d_approx):
            marker3d._offsets3d = ([0.0], [0.0], [float(s(d_approx))])
        else:
            marker3d._offsets3d = ([], [], [])

        # 2D Plot
        xL, xR = choose_x_range(x0)
        xs = np.linspace(xL, xR, 2000)
        with np.errstate(all="ignore"):
            ys_raw = np.asarray(f(xs), dtype=float)

        compact = should_compactify_y(ys_raw, threshold=1e3)

        if ax2d.legend_ is not None:
            ax2d.legend_.remove()

        if not compact:
            m = np.isfinite(xs) & np.isfinite(ys_raw)
            xs2, ys2 = xs[m], ys_raw[m]
            f_line2d.set_data(xs2, ys2)
            f_line2d.set_label("f(x)")

            if np.isfinite(d_approx):
                yt = f0 + d_approx * (xs - x0)
                mt = np.isfinite(yt)
                tan_line2d.set_data(xs[mt], yt[mt])
                tan_line2d.set_label("Tangente in x0")
            else:
                tan_line2d.set_data([], [])
                tan_line2d.set_label("Tangente (n/a)")

            pt2d.remove()
            pt2d = ax2d.scatter([x0], [f0], s=40, zorder=3, label="(x0, f(x0))")

            ax2d.set_title("f(x) und Tangente in x0 (linear)")
            ax2d.set_ylabel("f(x)")
            ax2d.set_xlim(xL, xR)

            if ys2.size > 0:
                lo, hi = np.percentile(ys2, [2, 98])
                if np.isfinite(lo) and np.isfinite(hi) and lo != hi:
                    pad = 0.15 * (hi - lo)
                    ax2d.set_ylim(lo - pad, hi + pad)

        else:
            ys = s(ys_raw)
            m = np.isfinite(xs) & np.isfinite(ys)
            xs2, ys2 = xs[m], ys[m]
            f_line2d.set_data(xs2, ys2)
            f_line2d.set_label("s(f(x))")

            g0 = float(s(f0))
            if np.isfinite(d_approx) and np.isfinite(f0):
                gprime = float(s_prime(f0) * d_approx)
                yt = g0 + gprime * (xs - x0)
                mt = np.isfinite(yt)
                tan_line2d.set_data(xs[mt], yt[mt])
                tan_line2d.set_label("Tangente an s(f) in x0")
            else:
                tan_line2d.set_data([], [])
                tan_line2d.set_label("Tangente (n/a)")

            pt2d.remove()
            pt2d = ax2d.scatter([x0], [g0], s=40, zorder=3, label="(x0, s(f(x0)))")

            ax2d.set_title("f(x) und Tangente in x0 (y kompaktifiziert)")
            ax2d.set_ylabel("s(·)")
            ax2d.set_xlim(xL, xR)

            ax2d.set_ylim(-1, 1)
            ax2d.set_yticks(ticks)
            ax2d.set_yticklabels(ticklabels)

        ax2d.legend(loc="best")

        suffix = " (f(x0) via Grenzwert)" if used_limit else ""
        mode = "2D: kompakt" if compact else "2D: linear"
        if np.isfinite(d_approx):
            status_text.set_text(
                f"f(x) = {expr_norm}   |   x0 = {x0:g}   |   approx f'(x0) ≈ {d_approx:.6g}{suffix}   |   {mode}"
            )
        else:
            status_text.set_text(
                f"f(x) = {expr_norm}   |   x0 = {x0:g}   |   approx f'(x0) n/a{suffix}   |   {mode}"
            )

        fig.canvas.draw_idle()

    btn_update.on_clicked(update)
    tb_f.on_submit(update)
    tb_x0.on_submit(update)

    update()
    plt.show()

if __name__ == "__main__":
    main()
