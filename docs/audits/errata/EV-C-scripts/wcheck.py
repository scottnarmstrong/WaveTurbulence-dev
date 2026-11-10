# w_p(theta) = int_0^inf <r theta + p>^{-2s} r^{d-3} dr, |p| = R, phi = angle(theta, -p_hat).
# <r theta + p>^2 = 1 + (r - R cos phi)^2 + R^2 sin^2 phi.  Pure-python Simpson in r = c + A sinh(t).
import math
def simpson(f, a, b, n=20000):
    if n % 2: n += 1
    h = (b - a) / n
    s = f(a) + f(b)
    for i in range(1, n):
        s += (4 if i % 2 else 2) * f(a + i*h)
    return s * h / 3
def w(d, s, R, phi):
    A = math.sqrt(1 + (R*math.sin(phi))**2)
    c = R*math.cos(phi)
    r0 = 1e4 * (abs(c) + A)
    g = lambda t: (lambda r: (A*A + (r-c)**2)**(-s) * max(r,0.0)**(d-3) * A*math.cosh(t))(c + A*math.sinh(t))
    t0, t1 = math.asinh(-c/A), math.asinh((r0 - c)/A)
    main = simpson(g, t0, t1)
    tail = r0**(d-2-2*s) / (2*s-d+2)          # int_{r0}^inf r^{d-3-2s} dr
    return main + tail
for d in (4, 5, 6):
    s = (d-2)/2 + 0.05
    print(f"d={d}, s={s:.2f}")
    for R in (10, 100, 1000):
        v = w(d, s, R, 0.0)
        print(f"   phi=0, R={R:5d}: w={v:.4g},  w/R^(d-3)={v/R**(d-3):.4g}")
    worst = 0
    for phi in (1e-3, 1e-2, 0.05, 0.1, 0.3, 0.7, 1.2, 1.6, 2.5, 3.1):
        m = max(w(d, s, R, phi) for R in (0.5, 1, 3, 10, 30, 100, 300, 1e3, 3e3, 1e4))
        ratio = m * min(1.0, phi**(d-3))
        worst = max(worst, ratio)
        print(f"   phi={phi:6.3f}: sup_R w = {m:.4g},  sup_R w*min(1,phi^(d-3)) = {ratio:.4g}")
    print("   worst ratio:", round(worst, 4))
