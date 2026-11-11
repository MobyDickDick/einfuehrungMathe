# Positive Differenzen und partielle Subtraktion

Stand: 11. November 2026. Ergebnis von Arbeitspaket 11 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Der Entwurf führt den in [11 – Multiplikation, Ordnung und Kürzbarkeit, Abschnitt 5](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/11_Multiplikation_Ordnung_und_Kuerzbarkeit.md) benannten Anschluss aus. Er steht neben dem Manuskript; LyX-Quellen, Exporte und Sicherungen wurden nicht verändert.

## 1. Anschlussstelle und Voraussetzungen

Es bleibt bei Deiner Festlegung \(\mathbb N=\{1,2,\ldots\}\). Subtraktion wird deshalb zunächst nur für diejenigen Zahlenpaare eingeführt, bei denen ein **positiver** Rest übrig bleibt. Die Existenz dieses Restes ist in der Additionsbeschreibung der Ordnung schon enthalten; neu zu begründen sind seine Eindeutigkeit und die darauf beruhenden Rechenregeln.

Der Entwurf kann nach den bisherigen Fortsetzungen zur Multiplikation und vor „Über die Anzahl der Begrüßungen“ eingefügt werden: [Zahlenteil 18868](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18868), beziehungsweise [22083](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22083) im zweiten Peano-Folgekapitel. Dort wird unmittelbar danach unter der Voraussetzung \(n>1\) die Differenz \(n-1\) gebraucht. Das Verhältnis der beiden Kapitel bleibt offen. Zeilenangaben bezeichnen LyX-Quellzeilen, keine Buchseiten.

Mathematisch hängt dieser Entwurf nur von Addition, Ordnung und den Nachfolgergrundlagen ab. Die Multiplikationsgesetze aus den vorherigen Entwürfen werden hier nicht gebraucht. Soll später die Reihenfolge im Manuskript geändert werden, wäre nach den geprüften Additionsgesetzen ebenfalls ein geeigneter Ort.

| Grundlage | Fundstelle und Verwendung |
| --- | --- |
| Nichtleere endliche Ketten eines festen Grundblocks | [03, Abschnitte 1 und 6](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/03_Begruendungskette_natuerliche_Zahlen.md). Vollständige und eindeutige Benennung dieser Ketten durch positive natürliche Zahlen bleibt vorausgesetzt. |
| Nachfolgerinjektivität: \(u+1=v+1\Rightarrow u=v\) | [Lemma bei 15503–15523](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15503), mit den in [03, Abschnitt 6](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/03_Begruendungskette_natuerliche_Zahlen.md) festgehaltenen Reparaturen aus der Kettengrundlage. Sie liefert den Anfang und den Schritt des Kürzungsbeweises. |
| Vollständige Induktion ab 1 | [03, Abschnitt 6](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/03_Begruendungskette_natuerliche_Zahlen.md). Induziert wird über den gemeinsamen Summanden, nicht über eine Differenz. |
| Addition mit dem Nachfolger: \(u+(v+1)=(u+v)+1\) | [16106](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16106), wiederholt [19282](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19282); Prüfung in [06, Abschnitt 2](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md). |
| Gleichheitserhaltung und Kommutativität der Addition | [06, Abschnitte 2 und 3](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md). Einsetzen gleicher Zahlen liefert die einfache Richtung der Kürzungsäquivalenz; Kommutativität die Linkskürzung und einige Umkehrregeln. |
| Positive Restdarstellung: \(a<b\iff\exists k\in\mathbb N:\ a+k=b\) | Bereits ausdrücklich in der [Additionsdefinition 13936–13950](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:13936). Erläuterung der Verbindung zur Kettenordnung in [11, Abschnitte 1 und 2](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/11_Multiplikation_Ordnung_und_Kuerzbarkeit.md). |
| Strenge Ordnung und ausschliessende Dreifallunterscheidung | [03, Abschnitte 2 und 3](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/03_Begruendungskette_natuerliche_Zahlen.md). Genau einer der Fälle \(a<b\), \(a=b\) und \(b<a\) gilt. |

Die örtlichen Reparaturen dieser Grundlagen sind vor einer späteren Übernahme mitzuführen. Insbesondere wird die Nachfolgerinjektivität aus dem Kürzen gleicher Grundzeichen gewonnen, nicht aus der hier erst zu beweisenden allgemeinen Additionskürzung. Die neue Induktion setzt deshalb ihre eigene Behauptung nicht voraus. Für die zusätzliche Regel zum Verschieben beider Zahlen in Abschnitt 4 wird auch die bereits geprüfte Assoziativität der Addition benutzt.

Der Ausdruck „Differenz“ kommt schon auf Kettenebene vor: [bei 2955–2973](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:2955) wird \(D\) aus \(BD=C\) so genannt. Die folgende Zahlendifferenz bezeichnet die Zahl dieser Restkette. Sie wird ausdrücklich an die geordnete Gleichung \(a+k=b\) gebunden.

## 2. Schreibentwurf: Einen gemeinsamen Summanden kürzen

**Beginn des vorgeschlagenen Manuskripttexts.** Die Ich-Form ist ein Formulierungsvorschlag im Anschluss an Deinen Text, keine neue persönliche Äusserung von Dir.

Bei den Symbolketten konnten wir sehen, was nach dem Wegnehmen eines Anfangsstücks übrig bleibt. Nun möchte ich diesem Rest eine Zahl zuordnen. Vorher muss ich aber zeigen, dass bei denselben beiden Zahlen nicht zwei verschiedene Reste herauskommen können.

Dass ich zu gleichen Zahlen dieselbe Zahl addieren darf, haben wir bereits behandelt. Jetzt brauche ich die umgekehrte Schlussrichtung.

### Satz: Ein gemeinsamer Summand lässt sich kürzen

Für \(a,b,c\in\mathbb N\) gilt

\[
a+c=b+c\quad\Longleftrightarrow\quad a=b.
\]

Ebenso gilt

\[
c+a=c+b\quad\Longleftrightarrow\quad a=b.
\]

**Beweis.** Die Richtung von \(a=b\) zur Gleichheit der Summen folgt durch Einsetzen gleicher Zahlen. Für die andere Richtung führe ich die vollständige Induktion über den gemeinsamen Summanden \(c\). Die Induktionsaussage lautet: Für alle \(a,b\in\mathbb N\) folgt aus \(a+c=b+c\) die Gleichheit \(a=b\).

Für \(c=1\) ist das gerade die Nachfolgerinjektivität: Aus \(a+1=b+1\) folgt \(a=b\). Damit ist der Anfang bewiesen.

Es sei nun die Aussage für ein beliebiges \(c\in\mathbb N\) bewiesen. Für beliebige \(a,b\in\mathbb N\) gelte

\[
a+(c+1)=b+(c+1).
\]

Nach der Regel für die Addition mit dem Nachfolger ist das

\[
(a+c)+1=(b+c)+1.
\]

Die Nachfolgerinjektivität liefert \(a+c=b+c\). Auf diese Gleichung kann ich die Induktionsannahme anwenden und erhalte \(a=b\). Damit gilt die Aussage auch für \(c+1\), also nach vollständiger Induktion für alle positiven natürlichen Zahlen \(c\).

Für den gemeinsamen ersten Summanden benutze ich die Kommutativität:

\[
c+a=c+b
\quad\Longleftrightarrow\quad
a+c=b+c
\quad\Longleftrightarrow\quad a=b.
\]

Damit sind beide Äquivalenzen bewiesen.

Ich habe hier keine Zahl subtrahiert. „Kürzen“ ist zunächst eine begründete Schlussregel: Aus gleichen Summen mit einem gemeinsamen Summanden folgen gleiche übrige Summanden.

**Kleiner Haltepunkt:** Die Additionskürzung ist bereits ein abgeschlossenes Stück. Nun lässt sich die Differenz eindeutig festlegen.

## 3. Schreibentwurf: Die Zahl des Reststücks

### Satz und Definition: Die positive Differenz

Es seien \(a,b\in\mathbb N\) mit \(a<b\). Dann gibt es genau eine Zahl \(k\in\mathbb N\) mit

\[
a+k=b.
\]

Diese Zahl nenne ich die **Differenz von \(b\) und \(a\)** und schreibe dafür \(b-a\).

**Existenz.** Aus \(a<b\) folgt nach der schon vorhandenen Ordnungsbeschreibung, dass es eine positive natürliche Zahl \(k\) mit \(a+k=b\) gibt. In der Kettenvorstellung ist sie die Zahl des nichtleeren Reststücks.

**Eindeutigkeit.** Gäbe es zwei solche Zahlen \(k\) und \(\ell\), so wäre

\[
a+k=b=a+\ell.
\]

Durch Kürzen des gemeinsamen ersten Summanden \(a\) folgt \(k=\ell\). Damit ist die Differenz eindeutig bestimmt.

Zum Beispiel ist \(3+4=7\). Daher ist \(7-3=4\). In einer Kette aus sieben gleichen Grundsymbolen bleibt nach dem Wegnehmen der ersten drei ein Rest aus vier Grundsymbolen.

### Auf welchen Zahlenpaaren ist die Subtraktion definiert?

Die Schreibweise \(b-a\) benutze ich hier genau dann, wenn \(a<b\). Genauer ist

\[
D=\{(b,a)\in\mathbb N\times\mathbb N\mid a<b\},
\qquad
\operatorname{sub}:D\longrightarrow\mathbb N,
\qquad (b,a)\longmapsto b-a.
\]

In diesem geordneten Paar steht die grössere Zahl zuerst. Die Subtraktion ist damit eine **partielle Operation** auf den positiven natürlichen Zahlen: Sie ist auf einem Teil der Zahlenpaare definiert.

Was geschieht mit den anderen Paaren? Für jedes \(k\in\mathbb N\) gilt wegen der positiven Restdarstellung \(a<a+k\). Eine Gleichung \(a+k=b\) würde deshalb immer \(a<b\) nach sich ziehen. Im Fall \(a=b\) ist das mit der Gleichheit unvereinbar; im Fall \(b<a\) mit der umgekehrten strengen Ordnung. In beiden Fällen gibt es keinen positiven natürlichen Rest.

Deshalb sind beispielsweise \(3-3\) und \(3-7\) in der hier eingeführten Operation nicht definiert. Mit einer später eingeführten 0 könnte man den Gleichheitsfall ergänzen; mit negativen Zahlen auch die umgekehrte Reihenfolge. Diese Erweiterungen sind eigene Schritte. Für die jetzige Definition reicht \(a<b\).

## 4. Schreibentwurf: Addition und Subtraktion rückwärts lesen

### Satz: Die Umkehrregeln

Für \(a,b\in\mathbb N\) mit \(a<b\) gilt

\[
a+(b-a)=b,
\qquad
(b-a)+a=b.
\]

Für beliebige \(a,k\in\mathbb N\) gilt

\[
(a+k)-a=k,
\qquad
(a+k)-k=a.
\]

**Beweis.** Die erste Gleichung ist die definierende Eigenschaft von \(b-a\); die zweite folgt durch Vertauschen der Summanden.

Bei \((a+k)-a\) ist zuerst der Definitionsbereich zu prüfen. Weil \(k\) positiv ist, gilt \(a<a+k\). Die Differenz ist also definiert. Die Gleichung \(a+k=a+k\) zeigt, dass \(k\) den gesuchten Rest liefert. Nach der Eindeutigkeit der Differenz gilt \((a+k)-a=k\).

Für die letzte Gleichung schreibe ich \(a+k=k+a\). Weil \(a\) positiv ist, folgt \(k<a+k\). Also ist auch \((a+k)-k\) definiert; die Gleichung \(k+a=a+k\) liefert jetzt \(a\) als eindeutigen Rest. Somit ist \((a+k)-k=a\).

Addition und Subtraktion lassen sich damit auf dem jeweils angegebenen Bereich rückgängig machen. Aus \(3+4=7\) folgen beispielsweise \(7-3=4\) und \(7-4=3\).

Auch die Differenz selbst kann ich wieder vom Ganzen abziehen. Für \(a<b\) gilt

\[
b-(b-a)=a.
\]

**Beweis.** Setze \(k=b-a\). Dann ist \(a+k=b\). Die soeben bewiesene Regel \((a+k)-k=a\) liefert \(b-(b-a)=a\). Zugleich zeigt \(k<a+k=b\), dass auch diese Subtraktion im Definitionsbereich liegt.

### Eine Gleichung mit einem fehlenden Summanden

Für feste \(a,b\in\mathbb N\) mit \(a<b\) und für jedes \(x\in\mathbb N\) gilt

\[
a+x=b\quad\Longleftrightarrow\quad x=b-a.
\]

**Beweis.** Erfüllt \(x\) die Gleichung, ist es der eindeutige positive Rest und deshalb gleich \(b-a\). Gilt umgekehrt \(x=b-a\), folgt durch Einsetzen in die definierende Gleichung \(a+(b-a)=b\) auch \(a+x=b\). Wegen der Kommutativität gilt dieselbe Aussage für \(x+a=b\).

Die Voraussetzung \(a<b\) gehört zu dieser Schreibweise. Ohne sie hat die Gleichung \(a+x=b\) keine Lösung in unseren positiven natürlichen Zahlen, und der Ausdruck \(b-a\) ist hier nicht definiert.

### Beide Zahlen um dasselbe Stück vergrössern

Für \(a<b\) und \(c\in\mathbb N\) gilt ausserdem

\[
(b+c)-(a+c)=b-a.
\]

**Beweis.** Setze wieder \(k=b-a\), sodass \(a+k=b\). Mit Assoziativität und Kommutativität der Addition folgt

\[
\begin{aligned}
(a+c)+k
 &=a+(c+k) &&\text{(Assoziativität)}\\
 &=a+(k+c) &&\text{(Kommutativität)}\\
 &=(a+k)+c &&\text{(Assoziativität)}\\
 &=b+c &&\text{(Einsetzen von }a+k=b\text{).}
\end{aligned}
\]

Weil \(k\) positiv ist, zeigt diese Gleichung zugleich \(a+c<b+c\). Die Differenz auf der linken Seite ist also definiert, und ihr eindeutiger Rest ist \(k=b-a\).

### Der Anschluss an den Vorgänger

Für \(n\in\mathbb N\) gilt

\[
(n+1)-1=n,
\qquad
(n+1)-n=1.
\]

Beides sind die Umkehrregeln mit den Summanden \(n\) und 1. Die erste Gleichung ist auf ganz \(\mathbb N\) als Aussage über \(n\) gültig, denn \(1<n+1\).

Für \(n>1\) ist auch \(n-1\) definiert. Aus seiner Definition und der Kommutativität folgt \((n-1)+1=n\): Die Differenz \(n-1\) ist also der schon behandelte Vorgänger. Bei \(n=1\) ist \(n-1\) innerhalb dieses Zahlbereichs nicht definiert. Genau deshalb ist die Voraussetzung \(n>1\) im folgenden Handschlagbeispiel hier passend.

**Ende des vorgeschlagenen Manuskripttexts.** Mit Definition, Definitionsbereich und Umkehrregeln ist das Arbeitspaket abgeschlossen.

## 5. Reichweite und konkrete Folgen für das Manuskript

Der Entwurf schliesst den in [06, Abschnitten 2 und 4](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md) dokumentierten Bedarf: Die Additionskürzung liegt als vollständiger Beweis vor, und \(b-a\) ist für \(a<b\) durch Existenz und Eindeutigkeit eingeführt. Die einfachen Umkehrregeln dürfen danach mit ausdrücklich geprüftem Definitionsbereich verwendet werden.

An zwei vorhandenen Stellen ergibt das einen konkreten Anschluss:

- **Handschlagaufgabe:** Bei [18905](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18905), wiederholt bei 22120, ist \(n-1\) wegen \(n>1\) nun begründet. Bei [19032](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19032), wiederholt bei 22247, kann \((n+1)-1=n\) direkt mit der bewiesenen Umkehrregel begründet werden. Die Voraussetzungen für die Division durch 2 und die bereits dokumentierte falsche Zwischenformel bleiben gesonderte Arbeiten.
- **Früherer Kommutativitätsbeweis der Addition:** Die Differenzen \(n_2-n_4\) und \(n_2-n_3\) stehen [bei 17161 und 17222](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17161), wiederholt bei 20356 und 20417. Der jetzige Entwurf rechtfertigt dort keine rückwirkende Verwendung: Er benutzt seinerseits bereits die geprüfte Kommutativität für die Linkskürzung. Für eine durchgehende Begründung bleibt der in [06, Abschnitt 3](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md) vorgeschlagene Ersatzbeweis ohne Subtraktion der passende Weg. Bei jeder Verwendung von \(n_2-n_3\) wäre zudem \(n_3<n_2\) ausdrücklich zu sichern.

Die Subtraktion ist nicht auf ganz \(\mathbb N\times\mathbb N\) definiert. Es wird weder \(a-a\) auf 1 oder eine andere positive Zahl gesetzt noch eine „abgeschnittene“ Subtraktion eingeführt. Die Erweiterung um 0 und eine dazu passende Erweiterung der Rechenoperationen bleiben offen. Ebenso sind allgemeine Regeln für ganze Zahlen und Brüche hier nicht behauptet.

Die nummerierte Aufgabenliste enthält nach diesem Paket keine weitere offene Fortsetzung. Die Übernahme der Entwürfe und örtlichen Korrekturen ins Manuskript bleibt als eigene Arbeit offen. Ein konkreter Vorschlag für die nächste Diskussion ist, den Ersatzbeweis der Additionskommutativität aus 06 und den ersten kleinen Multiplikationsabschnitt aus 09 gemeinsam zur Übernahme auszuwählen. Das ist eine örtlich begrenzte Auswahl, kein Auftrag zur Neufassung der abgeschlossenen Teile.

## 6. Fachliche Kontrolle und Abschluss

Die Additionsbeschreibung der Ordnung, das vorhandene Lemma zur Nachfolgerinjektivität, die Nachfolgerregel der Addition und die beiden Anschlussstellen wurden an der aktuellen LyX-Quelle geprüft. Auch die verwendeten Differenzen im früheren Kommutativitätsbeweis und im Handschlagbeispiel wurden abgeglichen.

Die Beweisabhängigkeiten sind:

| Ergebnis | Unmittelbar verwendete Grundlagen |
| --- | --- |
| Rechtskürzung der Addition | Induktion ab 1, Nachfolgerinjektivität, Nachfolgerregel der Addition. |
| Linkskürzung der Addition | Rechtskürzung und geprüfte Kommutativität der Addition. |
| Existenz der positiven Differenz | Positive Restdarstellung der strengen Ordnung. |
| Eindeutigkeit | Linkskürzung; vorher keine Subtraktion. |
| Ausschluss der anderen Zahlenpaare | Positive Restdarstellung und Ausschluss von Gleichheit bzw. strenger Gegenrichtung. |
| Umkehrregeln und fehlender Summand | Definition, Eindeutigkeit, Kommutativität; Definitionsbereiche jeweils mit positivem Rest geprüft. |
| Gemeinsames Vergrössern | Zusätzlich Assoziativität der Addition; die entstehende Gleichung liefert auch den positiven Rest für die neue Differenz. |

Im Induktionsschritt werden zunächst nur gleiche Nachfolger gekürzt. Erst danach wird die Induktionsannahme für den gemeinsamen Summanden \(c\) verwendet. Der Anfang \(c=1\) braucht keinen Summanden 0. Die Existenz der Differenz folgt aus der bereits vorhandenen Ordnung, nicht aus einer stillschweigend total definierten Subtraktion.

Die Randfälle sind ausdrücklich abgedeckt: Ein Rest 1 ist zulässig; \((n+1)-n=1\) gilt auch für \(n=1\). Bei gleichen Zahlen und bei einem grösseren zweiten Argument gibt es keinen positiven Rest. Beim Ausdruck \(b-(b-a)\) wird die zusätzlich nötige Ungleichung \(b-a<b\) durch den positiven verbleibenden Summanden \(a\) gesichert. Diese Kontrolle ist eine mathematische Durchsicht der ausgeschriebenen Beweise, keine maschinelle Formalisierung und kein neuer LyX-/PDF-Bau.

**Arbeitspaket 11 ist abgeschlossen:** Additionskürzung, Existenz und Eindeutigkeit positiver Differenzen, der genaue Definitionsbereich der partiellen Subtraktion sowie die Umkehrregeln liegen als örtlicher Schreibentwurf vor. Gleichheit und umgekehrte Ordnung sind als Grenzen der Operation in \(\mathbb N=\{1,2,\ldots\}\) begründet. Die Übernahme ins Manuskript bleibt offen.
