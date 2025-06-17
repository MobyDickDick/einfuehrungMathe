// Definition des Bereichs für t
t = 0.1:0.1:20;

// Definition der Funktionen
f1 = -4 * t ./ (1 + t);
f2 = -4 ./ (1 + t);

// Erstellen des Diagramms
clf(); // Grafikfenster löschen
plot(t, f1, 'r-'); // f1 in Rot
plot(t, f2, 'b-'); // f2 in Blau, gleiche Achsen
legend("f1 = -4*t / (1 + t)", "f2 = -4 / (1 + t)");
xlabel("t");
ylabel("Funktionswert");
title("Darstellung der Funktionen f1 und f2");
grid();
