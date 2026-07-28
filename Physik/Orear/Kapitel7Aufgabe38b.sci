function dy = system(t, y)
    m = 2;
    d = 3;
    k = 11;
    g = - 9.81;

    y1 = y(1); // s
    y2 = - y(2); // s'

    force = m * g + (1 - d / sqrt(d^2 + y1^2)) * k * y1;

    dy = [y2; force / m];
endfunction

// Parameter
m = 2;
d = 3;
k = 22;
g = 9.81;

// Zeitintervall
t = 0:0.01:10;
dt = t(2) - t(1);
Fs = 1 / dt;

// Neue Anfangsbedingungen: s(0) = 0, s'(0) = 0
y0 = [0; 0];

// Lösung berechnen
y = ode(y0, 0, t, system);

// Energie berechnen
s = y(1, :);
v = y(2, :);

L = sqrt(d^2 + s.^2);
E_kin = 0.5 * m * v.^2;
E_pot = m * g * s + 0.5 * k * (L - d).^2;
E_total = E_kin + E_pot;

// Visualisierung Zeitbereich
clf();
subplot(3,1,1);
plot(t, -s, 'b');
xlabel("Zeit [s]");
ylabel("s(t) [m]");
title("Auslenkung der Masse");

subplot(3,1,2);
plot(t, -v, 'r');
xlabel("Zeit [s]");
ylabel("s''(t) [m/s]");
title("Geschwindigkeit der Masse");

subplot(3,1,3);
plot(t, E_total, 'k');
xlabel("Zeit [s]");
ylabel("E_{gesamt}(t) [J]");
title("Gesamte mechanische Energie");

// ==== FOURIER-ANALYSE ====
N = length(s);
w = window('hm', N);                // Fensterfunktion (optional)
s_windowed = s .* w;

S = fft(s_windowed);         // FFT berechnen
f = Fs * (0:N-1)/N;          // Frequenzachse
S_mag = abs(S)/N;            // normierter Betrag
half = 1:floor(N/2);         // bis Nyquist

f_half = f(half);
S_half = 2 * S_mag(half);    // gespiegelt

// Plot des Spektrums
scf(); // neues Fenster
plot(f_half, S_half, 'g');
xlabel("Frequenz [Hz]");
ylabel("Amplitude");
title("Frequenzspektrum der Auslenkung s(t)");

// Optionale Anzeige der dominanten Frequenz
[peak, idx] = max(S_half);
dominante_freq = f_half(idx);
disp("Dominante Frequenz [Hz]: " + string(dominante_freq));

// === FOURIER-RECONSTRUKTION ====

// --- Fourier-Näherung rekonstruieren aus FFT ---

// Fensterung und FFT
N = length(s);
dt = t(2) - t(1);
Fs = 1 / dt;

w = window('hm', N);                
// Fensterfunktion (optional)
s_windowed = s .* w;

S = fft(s_windowed);
f = Fs * (0:N-1)/N;
S_mag = abs(S) / N;
S_phase = atan(imag(S), real(S)); // Phase

// Frequenzen und Koeffizienten für Rekonstruktion
half = 1:floor(N/2);
f_half = f(half);
S_half = 2 * S_mag(half);          // Betrag (Faktor 2: symmetrisch)
P_half = S_phase(half);           // Phase

// Rekonstruktion der Näherung mit den ersten M Termen
M = 10; // Anzahl der Fourier-Komponenten
s_recon = zeros(t); // leeres Signal

for n = 1:M
    s_recon = s_recon + S_half(n) * cos(2 * %pi * f_half(n) * t + P_half(n));
end

// Plot original vs. rekonstruiert
scf();
plot(t, s, 'b', t, s_recon, 'r--');
legend("Original s(t)", "Fourier-Näherung");
xlabel("Zeit [s]");
ylabel("s(t) [m]");
title("Rekonstruktion der Auslenkung aus Fourier-Komponenten");
