import numpy as np

# Gegebene Werte
G = 6.674e-11  # m^3 kg^-1 s^-2
M = 1.989e30   # kg
r0 = 6.96e8    # m
T0 = 27 * 24 * 3600  # Sekunden (27 Tage)

# Formel: r = (4 * pi^2 * r0^4) / (G * M * T0^2)
numerator = 4 * np.pi**2 * r0**4
denominator = G * M * T0**2
r_min = numerator / denominator

print(f"Minimalradius der Sonne: {r_min:.2f} Meter")

# Der minimale Radius beträgt etwa 12 km.