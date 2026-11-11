# Multiplikation, Ordnung und das Kürzen eines Faktors

Stand: 10. November 2026. Ergebnis von Arbeitspaket 10 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Dieses Paket führt den Schreibentwurf aus [10 – Distributivität und Assoziativität](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/10_Distributivitaet_und_Assoziativitaet.md) weiter. Es begründet die strenge Ordnungserhaltung bei der Multiplikation mit einer positiven natürlichen Zahl und daraus die Kürzungsregel. Der Entwurf steht neben dem Manuskript; LyX-Quellen, Exporte und Sicherungen wurden nicht verändert.

## 1. Anschlussstelle und Voraussetzungen

Der folgende Text schliesst an die Multiplikationsgesetze des vorherigen Entwurfs an. Für eine spätere Übernahme gehören die drei Entwürfe gemeinsam hinter die Multiplikationsdefinition und vor „Über die Anzahl der Begrüßungen“: [Zahlenteil 18843–18868](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18843), beziehungsweise [22058–22083](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22058) im zweiten Peano-Folgekapitel. Definitionen und Anschlussstellen wurden an der aktuellen Quelle geprüft. Zeilenangaben bezeichnen LyX-Quellzeilen, keine Buchseiten. Über das Verhältnis der beiden Kapitel ist weiterhin nicht entschieden.

Es bleibt bei Deiner Festlegung \(\mathbb N=\{1,2,\ldots\}\). Insbesondere ist jedes Produkt zweier natürlicher Zahlen wieder eine **positive** natürliche Zahl. Das folgt hier bereits daraus, dass die durch endliche Rekursion bestimmte Multiplikation eine Funktion \(\mathbb N\times\mathbb N\to\mathbb N\) ist. Es wird dafür kein zusätzlicher Satz über Produkte mit 0 benötigt.

Für den Anschluss sind folgende Grundlagen ausdrücklich festzuhalten:

| Grundlage | Fundstelle und Verwendung |
| --- | --- |
| Ordnung durch nichtleere Restketten | [Kettenordnung ab 2848](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:2848). Die Restkette besteht aus demselben festen Grundblock; ihre eindeutige Benennung durch eine positive natürliche Zahl gehört zur Kettengrundlage. |
| Positive Restdarstellung \(a<b\iff\exists k\in\mathbb N:\ b=a+k\) | Bereits ausdrücklich in der [Additionsdefinition 13936–13950](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:13936). Sie stimmt mit der Kettenordnung überein. |
| Vergleichbarkeit mit Ausschluss der Gegenfälle | [Übertragung der Ordnung ab 11736](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:11736) und [Dreifallunterscheidung bei 12549](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:12549). Die Reparatur aus [03, Abschnitt 3](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/03_Begruendungskette_natuerliche_Zahlen.md) begründet, dass **genau einer** der Fälle \(a<b\), \(a=b\), \(b<a\) gilt. |
| Nichtstrenge Ordnung | \(a\leq b\) bedeutet \(a<b\) oder \(a=b\); zur additiven Form siehe [18550–18579](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18550), wiederholt [21765–21794](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:21765). |
| Multiplikationsgesetze und Abschluss | Rekursionsgrundlage und Kommutativität aus [09, Abschnitte 2–3](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/09_Wiedereinstieg_Multiplikation.md); das erste Distributivgesetz aus [10, Abschnitt 2](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/10_Distributivitaet_und_Assoziativitaet.md). |

Die Kettengrundlage und die früher dokumentierten örtlichen Reparaturen bleiben Voraussetzungen für eine spätere Übernahme. Der neue Entwurf führt sie nicht nachträglich in die LyX-Quellen ein. Insbesondere darf beim Kürzungsbeweis nicht nur „mindestens einer der drei Fälle“ verwendet werden: Auch die Unvereinbarkeit von Gleichheit und strenger Ungleichheit sowie der beiden strengen Gegenrichtungen wird gebraucht.

Die neuen Beweise haben folgende Abhängigkeiten:

| Aussage | Unmittelbar benutzte Grundlagen |
| --- | --- |
| \(a<b\Rightarrow a\cdot c<b\cdot c\) | Positive Restdarstellung, \((a+k)\cdot c=a\cdot c+k\cdot c\), Abschluss des Produkts in \(\mathbb N\). |
| \(a<b\Rightarrow c\cdot a<c\cdot b\) | Vorige Aussage und Kommutativität der Multiplikation. |
| \(a\cdot c=b\cdot c\Rightarrow a=b\) | Strenge Ordnungserhaltung und ausschliessende Dreifallunterscheidung. |
| Kürzen in strengen und nichtstrengen Ungleichungen | Dieselben Grundlagen; der Gleichheitsfall benutzt Einsetzen gleicher Zahlen. |

Eine neue Induktion ist hier nicht erforderlich. Die Assoziativität der Multiplikation wird ebenfalls nicht benutzt. Subtraktion und Division werden für keinen dieser Schritte vorausgesetzt.

## 2. Schreibentwurf: Was geschieht mit der Reihenfolge?

**Beginn des vorgeschlagenen Manuskripttexts.** Die Ich-Form ist ein Formulierungsvorschlag im Anschluss an Deinen Text, keine neue persönliche Äusserung von Dir.

Wir können die Faktoren nun vertauschen, Summen ausmultiplizieren und drei Faktoren umklammern. Aber was geschieht mit der Reihenfolge zweier Zahlen, wenn ich beide mit derselben Zahl multipliziere?

Unsere natürlichen Zahlen beginnen weiterhin mit 1. Jeder Faktor, den ich hier verwende, ist also positiv. Zunächst erinnere ich daran, wie die Ordnung mit der Addition zusammenhängt.

### Die grössere Zahl hat ein nichtleeres Reststück

Für \(a,b\in\mathbb N\) gilt

\[
a<b\quad\Longleftrightarrow\quad
\text{es gibt ein }k\in\mathbb N\text{ mit }b=a+k.
\]

In den Symbolketten bedeutet das: An die Kette für \(a\) wird eine nichtleere Kette angehängt, und es entsteht die Kette für \(b\). Diese Restkette wird durch die positive natürliche Zahl \(k\) bezeichnet. Die Addition beschreibt genau dieses Anhängen. Umgekehrt macht das Anhängen einer solchen Restkette die ursprüngliche Kette echt länger; deshalb folgt aus \(b=a+k\) auch \(a<b\).

Insbesondere gilt für beliebige \(x,t\in\mathbb N\)

\[
x<x+t.
\]

Hier genügt \(t\) selbst als positiver Rest. Ich muss dafür noch keine Subtraktion ausführen. Im Gleichheitsfall \(a=b\) gibt es dagegen keinen solchen positiven Rest. Diesen Fall behandeln wir bei \(\leq\) gesondert.

### Satz: Ein gemeinsamer positiver Faktor erhält die strenge Ordnung

Es seien \(a,b,c\in\mathbb N\). Aus \(a<b\) folgt

\[
a\cdot c<b\cdot c
\qquad\text{und}\qquad
c\cdot a<c\cdot b.
\]

**Beweis.** Aus \(a<b\) folgt, dass es ein \(k\in\mathbb N\) mit \(b=a+k\) gibt. Für dieses \(k\) gilt

\[
\begin{aligned}
b\cdot c
 &=(a+k)\cdot c &&\text{(Einsetzen von }b=a+k\text{)}\\
 &=a\cdot c+k\cdot c &&\text{(Distributivgesetz).}
\end{aligned}
\]

Das Produkt \(k\cdot c\) ist wieder eine natürliche Zahl und somit positiv. In der letzten Gleichung steht also \(b\cdot c\) als Summe aus \(a\cdot c\) und einem positiven Rest. Nach der Ordnungsbeschreibung folgt daraus

\[
a\cdot c<b\cdot c.
\]

Wegen der bereits bewiesenen Kommutativität gilt dann auch

\[
c\cdot a=a\cdot c<b\cdot c=c\cdot b.
\]

Damit sind beide Behauptungen bewiesen.

Beispielsweise ist \(5=2+3\). Beim Multiplizieren mit 4 liefert das Distributivgesetz

\[
5\cdot4=2\cdot4+3\cdot4=8+12.
\]

Der positive Rest ist nun \(3\cdot4=12\); deshalb gilt \(2\cdot4<5\cdot4\). Es kommt darauf an, dass der Rest nach der Multiplikation positiv bleibt.

**Kleiner Haltepunkt:** Die strenge Ordnungserhaltung ist damit vollständig begründet. Mit dem folgenden Satz lässt sich auch das Kürzen eines gemeinsamen Faktors erklären.

## 3. Schreibentwurf: Gleiche Produkte und gleiche Faktoren

### Satz: Ein gemeinsamer positiver Faktor lässt sich kürzen

Es seien \(a,b,c\in\mathbb N\). Dann gilt

\[
a\cdot c=b\cdot c\quad\Longleftrightarrow\quad a=b.
\]

Ebenso gilt

\[
c\cdot a=c\cdot b\quad\Longleftrightarrow\quad a=b.
\]

**Beweis.** Zunächst nehme ich \(a\cdot c=b\cdot c\) an. Nach der Vergleichbarkeit unserer natürlichen Zahlen gilt genau einer der drei Fälle

\[
a<b,\qquad a=b,\qquad b<a.
\]

Im ersten Fall würde nach dem vorherigen Satz \(a\cdot c<b\cdot c\) gelten. Das widerspricht der angenommenen Gleichheit der Produkte. Im dritten Fall würde entsprechend \(b\cdot c<a\cdot c\) gelten; auch das widerspricht ihrer Gleichheit. Es bleibt nur \(a=b\).

Umgekehrt folgt aus \(a=b\) durch Einsetzen gleicher Zahlen sofort \(a\cdot c=b\cdot c\). Damit ist die erste Äquivalenz bewiesen.

Für den gemeinsamen ersten Faktor verwende ich die Kommutativität:

\[
c\cdot a=c\cdot b
\quad\Longleftrightarrow\quad
a\cdot c=b\cdot c
\quad\Longleftrightarrow\quad a=b.
\]

Damit ist auch die zweite Äquivalenz bewiesen.

Das Wort „kürzen“ beschreibt hier eine Schlussregel für die Gleichung: Aus gleichen Produkten mit demselben positiven Faktor darf ich auf die Gleichheit der übrigen Faktoren schliessen. Ich habe dafür durch keine Zahl dividiert. Die Regel ist bereits begründet, bevor wir eine Division einführen.

## 4. Schreibentwurf: Auch Ungleichungen lassen sich zurücklesen

Aus einer Reihenfolge der Faktoren folgt eine Reihenfolge der Produkte. Gilt auch die umgekehrte Richtung? Für unseren positiven gemeinsamen Faktor lautet die Antwort ja.

### Folgerung: Den gemeinsamen Faktor in einem Vergleich kürzen

Für \(a,b,c\in\mathbb N\) gilt

\[
a<b\quad\Longleftrightarrow\quad a\cdot c<b\cdot c
\]

und

\[
a\leq b\quad\Longleftrightarrow\quad a\cdot c\leq b\cdot c.
\]

Beide Aussagen gelten ebenso mit \(c\) als gemeinsamem ersten Faktor.

**Beweis.** Für die erste Äquivalenz ist die Richtung von links nach rechts schon bewiesen. Sei nun \(a\cdot c<b\cdot c\). Wieder unterscheide ich die drei Fälle für \(a\) und \(b\). Wäre \(a=b\), so wären durch Einsetzen auch die Produkte gleich. Wäre \(b<a\), so folgte aus der strengen Ordnungserhaltung \(b\cdot c<a\cdot c\). Beide Möglichkeiten sind mit der angenommenen strengen Ungleichung unvereinbar. Also gilt \(a<b\).

Für die zweite Äquivalenz benutze ich die Bedeutung von \(\leq\): Aus \(a\leq b\) folgt entweder \(a<b\) oder \(a=b\). Im ersten Fall folgt die entsprechende strenge Produktungleichung, im zweiten die Produktgleichheit. In beiden Fällen ist \(a\cdot c\leq b\cdot c\).

Gilt umgekehrt \(a\cdot c\leq b\cdot c\), so sind die Produkte entweder streng geordnet oder gleich. Im strengen Fall liefert die erste Äquivalenz \(a<b\); im Gleichheitsfall liefert der Kürzungssatz \(a=b\). Damit gilt jeweils \(a\leq b\).

Durch Vertauschen der Faktoren gelten alle diese Schlüsse auch für \(c\cdot a\) und \(c\cdot b\).

**Ende des vorgeschlagenen Manuskripttexts.** Der Kern des Pakets ist bereits mit der strengen Ordnungserhaltung und dem Gleichheitskürzungssatz abgeschlossen. Die kurze Folgerung zeigt zusätzlich, wie die Regel auf Vergleiche angewendet wird.

## 5. Reichweite und nächster Anschluss

Zusammen mit den beiden vorherigen Entwürfen sind nun die Einsregeln, die Nachfolgerregel im zweiten Faktor, Kommutativität, beide Distributivgesetze, Assoziativität sowie Ordnungserhaltung und Kürzbarkeit positiver Faktoren ausgearbeitet. Insbesondere ist der in [06, Abschnitt 4](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md) skizzierte Ordnungs- und Kürzungsbeweis damit ausgeschrieben.

Alle Aussagen dieses Entwurfs betreffen \(\mathbb N=\{1,2,\ldots\}\). Bei einer späteren Erweiterung auf \(\mathbb N_0\) muss der gemeinsame Faktor für die strengen Vergleiche und die Kürzungsregel weiterhin positiv bleiben. Sobald \(n\cdot0=0\) eingeführt wäre, würde beispielsweise \(1\cdot0=2\cdot0\) gelten, obwohl \(1\ne2\). Der Nullfaktor ist deshalb kein zusätzlicher Fall des hier bewiesenen Kürzungssatzes. Für ganze oder rationale Zahlen wären die erweiterten Operationen und ihre Ordnungsregeln gesondert zu begründen.

Fortschreibung vom 11. November 2026: Der folgende Anschluss ist inzwischen als Arbeitspaket 11 in [12 – Positive Differenzen und partielle Subtraktion](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/12_Positive_Differenzen_und_partielle_Subtraktion.md) vollständig ausgearbeitet. Der nächste Absatz hält den ursprünglichen Anschlussplan fest.

Als nächster begrenzter Anschluss bietet sich die bereits in [06, Abschnitte 2 und 4](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md) dokumentierte **positive Differenz und partielle Subtraktion** an: zunächst die Additionskürzung ausdrücklich beweisen, dann für \(a<b\) den eindeutigen positiven Rest \(k\) aus \(a+k=b\) als \(b-a\) bezeichnen und die zugehörigen Umkehrregeln ausarbeiten. Dafür braucht es keine Erweiterung des Zahlbereichs. Gleichheit und umgekehrte strenge Ordnung markieren die späteren Erweiterungsschritte zu 0 und negativen Zahlen. Dieser Anschluss ist in der Aufgabenliste als Arbeitspaket 11 vorgemerkt und hier noch nicht ausgearbeitet.

Die anschliessende Handschlagaufgabe benutzt darüber hinaus Subtraktion, Teilbarkeit durch 2 und Bruchrechnung; die in [10, Abschnitt 4](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/10_Distributivitaet_und_Assoziativitaet.md) festgehaltene Korrekturstelle bleibt bestehen. Die vorliegenden Entwürfe und die örtlichen Korrekturen müssen vor einer durchgehenden Verwendung im Manuskript noch übernommen werden.

## 6. Fachliche Kontrolle und Abschluss

Bei der Durchsicht wurden die Ordnungsdefinitionen, die Übertragung von Ketten auf Zahlen und beide Anschlussstellen an der aktuellen Quelle abgeglichen. Die positive Restdarstellung ist im Manuskript bereits ausdrücklich vorhanden; der Entwurf erläutert ihre Verbindung zur Kettenordnung und führt keine abweichende Ordnung ein.

Der entscheidende Schritt verwendet \(k\cdot c\in\mathbb N\) als Zeugen für die strenge Produktungleichung. Seine Positivität stammt aus dem Zielbereich der rekursiv definierten Multiplikation, nicht aus dem erst zu beweisenden Ordnungssatz. Die Gleichheitskürzung folgt erst danach durch Vergleichbarkeit; sie wird beim Beweis der Ordnungserhaltung nicht vorausgesetzt. Auch die Rückrichtungen der beiden Ordnungsäquivalenzen sind ausgeschrieben. Es wird weder mit einer unbewiesenen Division noch mit der Schreibweise \(b-a\) argumentiert.

Die Randfälle sind von den allgemeinen Argumenten erfasst: Für \(c=1\) sind die Produkte nach den Einsregeln die ursprünglichen Zahlen; für \(b=a+1\) ist der Rest \(k=1\) und der Produktrest \(1\cdot c=c\); für \(a=b\) wird beim nichtstrengen Vergleich der Gleichheitsfall verwendet. Der Gegenfall \(b<a\) wird im Kürzungsbeweis ausdrücklich ausgeschlossen. Das ist eine mathematische Durchsicht der ausgeschriebenen Beweise, keine maschinelle Formalisierung und kein neuer LyX-/PDF-Bau.

**Arbeitspaket 10 ist abgeschlossen:** Strenge Ordnungserhaltung und Kürzbarkeit eines positiven gemeinsamen Faktors liegen mit Anschlussstellen, Ordnungsgrundlage, vollständigen Beweisen und einem kleinen Haltepunkt als Schreibentwurf vor. Ergänzend sind die Kürzungsregeln für strenge und nichtstrenge Ungleichungen begründet. Die Übernahme ins Manuskript bleibt offen.
