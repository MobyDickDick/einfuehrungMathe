# Rechnen, Induktionsanwendungen und Zahlbereiche

Stand: 4. November 2026. Ergebnis von Arbeitspaket 5 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Grundlage sind die aktuell durch `EinfuehrungMathe.lyx` eingebundenen LyX-Quellen, einschliesslich der vorhandenen lokalen Änderungen im Zahlenteil. Zeilenangaben bezeichnen diese Quellen, keine Buchseiten oder älteren TeX-Exporte. Die Prüfung steht neben dem Manuskript; Manuskript, PDF, Sicherungen und Autosavedateien wurden nicht verändert.

Fortschreibung vom 11. November 2026: Die beiden örtlichen Assoziativitätskorrekturen und der Induktionsersatz für den Additionskommutativitätsbeweis aus den Abschnitten 2–3 sind in beide Peano-Folgekapitel übernommen. Einzelheiten und aktuelle Fundstellen stehen in [13 – Erste örtliche Übernahme ins Manuskript](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/13_Erste_oertliche_Uebernahme_ins_Manuskript.md). Die übrigen Befunde bleiben als Übernahmearbeiten offen; die folgenden Zeilenangaben bezeichnen den damaligen Prüfstand.

## 1. Ergebnis und Reichweite

**Die Addition durch Verketten und die rekursive Multiplikation passen zu deiner Zahlenidee. Die üblichen Rechengesetze lassen sich daran anschliessen.** Bei der Addition sind mehrere Beweise bereits im Kern richtig. Der ausgeschriebene Kommutativitätsbeweis enthält dagegen tatsächlich falsche Gleichungen. Beim Handschlagbeispiel stimmen die Formel und die Induktionsidee; eine Zwischenzeile verliert einen Summanden. Die Darstellung der Zahlbereiche braucht eine fachliche Berichtigung: rational und irrational schliessen sich innerhalb der reellen Zahlen aus; imaginär ist ein anderer Begriff.

| Gegenstand | Einordnung | Was zu tun ist |
| --- | --- | --- |
| Natürliche Zahlen beginnen bei 1 | Eigene, zulässige Festlegung | Beibehalten; bei Hilfsgrössen 0 und `ℕ₀` ausdrücklich unterscheiden. |
| Addition durch Verketten | Tragfähige Definition unter der Kettengrundlage aus Arbeitspaket 2 | Existenz, eindeutige Benennung und festes Grundsymbol ausdrücklich festhalten. |
| Gleichheitserhaltung, Addition mit dem Nachfolger, Assoziativität | Richtige Behauptungen; örtliche Begründungs- bzw. Schlussfehler | Vorhandene Beweise mit kleinen Eingriffen schliessen. |
| Kommutativitätsbeweis der Addition | Richtiger Satz, aber falsche Zwischenformeln und unklarer Induktionsablauf | Durch eine vollständige Zeichenverschiebung oder den unten angegebenen Induktionsschritt ersetzen. |
| Multiplikation | Richtige Rekursionsgleichungen; Rechengesetze noch nicht ausgearbeitet | Rekursionsgrundlage nennen; verwendete Gesetze beweisen oder vorläufig voraussetzen. |
| Subtraktion, Division, Potenzen | Stellenweise vor ihrer Einführung verwendet | Bereiche, Teilbarkeit und Nichtnullbedingungen ergänzen. |
| Starke Induktion und spätere Gleichheitsbeweise | Richtige Zielaussagen; einzelne falsche Schritte bzw. verdeckte Voraussetzungen | Grenzen der Induktionsannahme und Grundgleichheit präzisieren. |
| Handschlagformel | Richtig; eine Gleichung falsch | Links ebenfalls `+n` ergänzen; verwendete Rechenregeln benennen. |
| Zahlbereiche | Mehrere falsche Einordnungen; einige richtige Einschlüsse | Die reellen Zahlen ausdrücklich zwischen rational/irrational und komplex einordnen. |
| ggT, kgV und Irrationalität von √2 in `Restposten.lyx` | Richtige Grundideen; zusätzliche Formel- und Begründungsfehler | Definitionen vereinheitlichen, Euklid-Terminierung ergänzen, Primfaktor- und Paritätsargumente schliessen. |

Geprüft wurden die Addition ab Zeile 13887, die beiden Fassungen von „Schlussfolgerungen aus den Axiomen von Peano“, die Zahlbereichsübersicht und die unmittelbar einschlägigen Abschnitte in `Restposten.lyx`: Bruchrechnung, ggT, Euklid, Min/Max, kgV, Prozentrechnung sowie der Beweis zu √2 und seine Einordnung. Ergänzend ist die unmittelbar vor der Addition stehende Zuordnung zu Anfangsstückmengen unten erfasst. Die Grundlagenprüfung bis Peano bleibt in [Arbeitspaket 2](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/03_Begruendungskette_natuerliche_Zahlen.md); Quantoren und Mengenbildung bleiben in [Arbeitspaket 4](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/05_Mengenlehre_und_Quantoren.md) dokumentiert.

Dies ist keine vollständige Prüfung der Analysis in den Restposten, der Potenzreihen oder sämtlicher arithmetisch dargestellter Logikbeweise mit Kronecker-Symbolen. Die historischen und entwicklungsbezogenen Aussagen gehören zu Arbeitspaket 6. Über die beabsichtigte Funktion der doppelten Kapitel und ihre Entfernung wird hier nicht entschieden; das gehört zu Arbeitspaket 7. Die mathematisch wiederholten Stellen sind berücksichtigt.

## 2. Addition: Was die Definition bereits leistet

**Fundstellen:** [Definition 13887–13950](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:13887), [erneut 16066–16079](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16066) und [19242 ff.](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19242).

Zur übersichtlichen Besprechung sei hier `W_A(n)=n·A` die durch `n` bezeichnete Kette aus einem festen nichtleeren Grundblock `A`. Das ist eine Abkürzung dieser Notiz, kein Vorschlag, deine gesamte Notation zu ersetzen. Dann lautet deine Definition:

\[
W_A(m+n)=W_A(m)W_A(n).
\]

Die rechte Seite ist wieder eine nichtleere endliche Kette aus demselben Grundblock. Nach der Voraussetzung, dass sämtliche solchen Ketten eindeutig durch Zahlen bezeichnet werden, gibt es genau eine Zahl `m+n`. Damit sind **Existenz, Eindeutigkeit und Abschluss in ℕ** begründet. Die eindeutige Zerlegung in die vereinbarten Grundblöcke und die Benennung aller Ketten stammen aus der Grundlage von Arbeitspaket 2; die Gleichung allein beweist sie nicht neu. Ein Wechsel von `A` zu einem anderen festen Grundblock ersetzt blockweise und erhält Verkettung und Nachfolger. Deshalb hängt die erhaltene Zahl nicht von der Wahl dieses Blocks ab.

Das Beispiel mit drei und zwei Eseln [bei 13975–14007](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:13975) ergibt richtig fünf Esel. Bei 14001 steht zwischen den beiden Ketten zusätzlich ein `·`, obwohl dort Verkettung gemeint ist. Das sollte in der Schreibweise der folgenden Zeilen als blosse Verkettung erscheinen; eine Multiplikation zweier Ketten ist hier nicht definiert.

Auch die Ordnung passt: `m<n` genau dann, wenn `n=m+k` für ein **positives** `k∈ℕ`; das entspricht einem nichtleeren Reststück. Für `≤` muss Gleichheit als eigener Fall hinzukommen. Deine Wahl `0∉ℕ` ist gerade mit dieser Formulierung vereinbar.

### Gleichheitserhaltung ist richtig und noch keine Kürzungsregel

Das [Lemma 14024–14219](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:14024) zeigt richtig: Aus `n₁=n₂` folgen `n₁+n₃=n₂+n₃` und `n₃+n₁=n₃+n₂`. Es genügt, die gleichen Ketten in den beiden Argumentstellen einzusetzen und dann die Zahlengleichheit abzulesen. Dass `A` „fast beliebig“ sei, ist für diesen Schluss nicht erforderlich: Ein festes zulässiges `A` reicht. Der letzte Rückschluss benutzt die festgelegte Zahlengleichheit über Ketten, nicht allein die Additionsdefinition.

Für spätere Subtraktion wird ausserdem die **umgekehrte** Richtung gebraucht: Aus `a+c=b+c` folgt `a=b`. Das ist nicht dasselbe Lemma. Man kürzt an den gleichen Ketten die gleiche endliche Endkette `W_A(c)` und verwendet die eindeutige Zerlegung. Alternativ folgt es durch wiederholte Nachfolgerinjektivität. Die entsprechende Linkskürzung funktioniert ebenso. Beides benötigt die Kettengrundlage, keine bereits definierte Subtraktion.

### Addition mit dem Nachfolger und Assoziativität

Der Satz [16106](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16106), wiederholt bei [19282](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19282), ist richtig:

\[
n+(m+1)=(n+m)+1.
\]

Der Kettenbeweis verwendet nur Additionsdefinition, `W_A(m+1)=W_A(m)A`, Einsetzen gleicher Ketten, Assoziativität der Verkettung und den Rückschluss auf Zahlengleichheit. Er setzt die erst anschliessend bewiesene allgemeine Assoziativität der **Addition** nicht voraus.

Beim [ersten Assoziativitätsbeweis ab 16464](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16464) wird über `c=n₃` induziert; `a=n₁` und `b=n₂` sind beliebige festgehaltene Parameter. Der Anfang `c=1` ist der vorangehende Satz. Der vollständige Schritt ist:

\[
\begin{aligned}
a+(b+(c+1))
 &=a+((b+c)+1)\\
 &=(a+(b+c))+1\\
 &=((a+b)+c)+1\\
 &=(a+b)+(c+1).
\end{aligned}
\]

Die erste, zweite und letzte Umformung benutzen den Nachfolgersatz; nur die dritte benutzt die Induktionsannahme. Bei [16567–16580](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16567), entsprechend [19754–19767](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19754), wird eine Anwendung des Nachfolgersatzes fälschlich „Induktionsvoraussetzung“ genannt. Die dortige Gleichung ist richtig, ihre genannte Rechtfertigung ist zu ersetzen. Die wirkliche Induktionsannahme wird anschliessend passend benutzt.

Der [zweite Beweis ab 16700](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16700) ist ebenfalls ein passender direkter Weg: Beide Gruppierungen ergeben dieselbe verkettete Kette. In der Schlusszeile [17004](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17004), wiederholt [20195](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:20195), steht jedoch dieselbe Gruppierung auf beiden Seiten. Diese reflexive Gleichung ist wahr, aber noch nicht die Behauptung. Dort muss beispielsweise stehen:

\[
W_A((a+b)+c)=W_A(a+(b+c)),
\]

gefolgt von `(a+b)+c=a+(b+c)`. Die vorangehenden Schritte liefern diese Korrektur bereits.

## 3. Kommutativität: Der Satz stimmt, die Zeichenverschiebung noch nicht

**Fundstellen:** [17074–17281](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17074), wiederholt [20269 ff.](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:20269).

Hier sind drei verschiedene Probleme auseinanderzuhalten:

1. **Falscher Index im Anfang:** Bei [17139](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17139), ebenso [20334](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:20334), steht `n₁+1=1+n₂`, obwohl `n₂=1` gesetzt ist. Für `n₁=2` ergäbe das `3=2`. Richtig ist `n₁+1=1+n₁`; genau das liefert die vorhergehende Kettengleichung.
2. **Falsche Restlänge:** Bei [17166–17175](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17166), ebenso [20361–20370](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:20361), wird `n₃=1` gesetzt und danach `W_A(n₂)=W_A(n₃)A` verwendet. Das gilt damit nur für `n₂=2`, nicht für beliebiges `n₂>1`. Der Rest müsste zunächst der eindeutig bestimmte Vorgänger von `n₂` sein.
3. **Ein Zeichen wird hinzugefügt:** Bei [17200](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17200), ebenso [20395](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:20395), steht `W_A(n₁)W_A(n₃)=A W_A(n₁)W_A(n₃)`. Für `n₁=n₃=1` heisst das `AA=AAA`. Beim Verschieben muss das vorhandene `A` auf **beiden** Seiten vorkommen: `W_A(n₁)W_A(n₃)A=A W_A(n₁)W_A(n₃)`.

Die angestrebte Zwischenform bei 17161 ist für `1≤n₄<n₂` sachlich richtig. Im ausgeschriebenen Ablauf wechseln aber `n₃`, `n₄` sowie bereits verschobener Teil und Rest ihre Rollen. „Beliebig lange durchspielen“ ersetzt nicht die Angabe, welcher Rest kleiner wird und wann der Vorgang endet. Ausserdem wird dafür Subtraktion vor ihrer Definition benutzt.

**Reparatur mit deiner Zeichenidee:** Zwei nichtleere Ketten aus demselben Grundblock dürfen nach dem früheren Kettenlemma ihre Reihenfolge tauschen. Deshalb folgt direkt `W_A(a+b)=W_A(a)W_A(b)=W_A(b)W_A(a)=W_A(b+a)`. Dies ist unter der ausdrücklich benannten Kettengrundlage ein direkter Beweis, ohne Subtraktion.

**Reparatur als Induktionsübung:** Soll hier bewusst die Zahleninduktion geübt werden, halte `a` beliebig fest und induziere über `b`. Der Anfang `a+1=1+a` ist bereits [bei 14226–14289](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:14226) begründet. Mit `a+b=b+a` gilt:

\[
\begin{aligned}
a+(b+1)&=(a+b)+1=(b+a)+1\\
       &=b+(a+1)=b+(1+a)=(b+1)+a.
\end{aligned}
\]

Verwendet werden der Nachfolgersatz, die Induktionsannahme, die bereits bewiesene Assoziativität und der Anfangssatz mit 1. Die zu beweisende allgemeine Kommutativität wird nicht vorausgesetzt.

## 4. Multiplikation, Subtraktion und Division

### Die Multiplikationsdefinition ist passend

**Fundstellen:** [18843–18860](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18843), wiederholt [22058–22075](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22058).

\[
1\cdot n=n,\qquad (m+1)\cdot n=m\cdot n+n
\]

ist eine richtige Rekursion **im ersten Argument** für positive natürliche Zahlen. Es fehlt hier kein Anfang bei 0. Für festes `n` wird mit `n` begonnen und bei jedem Nachfolgerschritt `n` addiert. Abschluss und eindeutiger endlicher Aufbau ermöglichen die Definition; dass beliebige solche Rekursionen genau eine Funktion liefern, gehört zur vorausgesetzten Rekursionsgrundlage. Die Eindeutigkeit lässt sich sofort induktiv zeigen: Zwei Funktionen mit demselben Anfang und demselben Übergang stimmen zunächst bei 1 und dann bei jedem Nachfolger überein. Die Existenz erhält man durch den endlichen Aufbau der wiederholten Summen. Das ist dieselbe Art von Grundlage, die Arbeitspaket 2 bei Ketten verlangt. Ein formales Vergleichsbeispiel für Induktion und Rekursion bietet [Theorem Proving in Lean, Abschnitt 7.4](https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/#defining-the-natural-numbers); dort beginnt `Nat` bei 0. Diese andere Konvention wird nicht auf dein Skript übertragen.

Das frühere `m·A` baut eine **Kette**, das neue `m·n` ergibt eine **Zahl**. Diese beiden Verwendungen des Punkts dürfen erläutert werden, ohne eine davon streichen zu müssen. Der Anschluss lautet: `W_A(m·n)` ist die Verkettung von `m` Kopien des Blocks `W_A(n)`. Das folgt durch Induktion über `m` aus genau deinen beiden Rekursionsgleichungen und der Additionsdefinition.

### Welche Rechengesetze später noch gebraucht werden

Die Rekursion macht Kommutativität, Assoziativität oder Distributivität nicht zu weiteren Definitionen. Diese sind zu beweisen, bevor sie als hergeleitete Regeln benutzt werden. Ein widerspruchsfreier Aufbau ist:

| Schritt | Begründung aus den vorherigen Schritten |
| --- | --- |
| `m·1=m` | Induktion über `m`; Anfang `1·1=1`, Schritt `(m+1)·1=m·1+1=m+1`. |
| `m·(n+1)=m·n+m` | Induktion über `m`. Im Schritt entstehen `m·n+m+n+1` und `m·n+n+m+1`; die Additionsgesetze gleichen sie an. |
| `m·n=n·m` | Induktion über `m`. Anfang `1·n=n=n·1`; Schritt `(m+1)·n=m·n+n=n·m+n=n·(m+1)`. |
| `(a+b)·c=a·c+b·c` | Induktion über `b`, Anfang `b=1` aus der Rekursion, Schritt durch einmaliges Addieren von `c`. |
| `a·(b+c)=a·b+a·c` | Aus der vorigen Distributivität und der Multiplikationskommutativität. |
| `(a·b)·c=a·(b·c)` | Induktion über `a`: Im Schritt `((a+1)·b)·c=(a·b+b)·c=(a·b)·c+b·c=a·(b·c)+b·c=(a+1)·(b·c)`. |

Dies sind örtliche Ergänzungsvorschläge zur Schliessung der Abhängigkeiten, noch keine Neufassung des Multiplikationskapitels. Für die späteren Ordnungs- und Teilbarkeitsargumente kommt hinzu: Multiplikation mit einer positiven natürlichen Zahl erhält strenge Ordnung. Denn aus `b=a+k`, `k∈ℕ`, folgt `b·c=a·c+k·c>a·c`. Daraus folgt auch Kürzbarkeit eines positiven Faktors. Für `ℕ₀` braucht es ergänzende Festlegungen `0+n=n`, `0·n=n·0=0`; für ganze und rationale Zahlen eine Erweiterung der Operationen oder eine ausdrücklich angekündigte vorläufige Voraussetzung.

### Subtraktion ist in deinen natürlichen Zahlen nur teilweise möglich

Im Kommutativitätsbeweis werden `n₂−n₄` und `n₂−n₃` verwendet; im Handschlagbeispiel `n−1`. Bei `ℕ={1,2,…}` lässt sich für `a>b` die Differenz `a−b` als die eindeutige Zahl `k∈ℕ` mit `b+k=a` definieren. Existenz folgt aus der Ordnung, Eindeutigkeit aus Additionskürzung. Für `a=b` ist das Ergebnis 0 und liegt somit erst in `ℕ₀` oder `ℤ`; für `a<b` benötigt man `ℤ`. Die Schranke `1≤n₄<n₂` sichert eine positive Differenz, die Schranke allein ist aber noch keine Definition der Operation.

Entsprechend ist `a/b` in `ℕ` nur dann eine natürliche Zahl, wenn `b` ein Teiler von `a` ist. Für allgemeines Bruchrechnen wird in `ℚ` gerechnet; der Nenner muss ungleich 0 sein. `a mod b` ist wiederum der Rest bei der Division mit Rest, kein Bruch. Bei positiven `a,b` liegt er in `ℕ₀`, denn 0 kann auftreten. Aus `ℕ₀` als Hilfsbereich folgt nicht `0∈ℕ`.

Ein kurzer Hilfssatz liefert die später benötigte Division mit Rest ohne vorherige Bruchdivision: Für `a∈ℕ₀`, `b∈ℕ` betrachte `Q={q∈ℕ₀ | qb≤a}`. Die Menge enthält 0 und liegt wegen `b≥1` in der endlichen Menge `{0,…,a}`. Sei `q` ihr Maximum und `r=a−qb∈ℕ₀`. Wäre `r≥b`, wäre auch `(q+1)b≤a`, entgegen der Maximalität. Also `0≤r<b`. Gäbe es eine zweite Zerlegung `a=q'b+r'` mit denselben Restschranken und etwa `q'>q`, folgte `q'b≥qb+b>qb+r=a`, ein Widerspruch. Daher `q'=q` und dann `r'=r`. Hier werden die bereits begründete positive Multiplikationsordnung und die Erweiterung auf `ℕ₀` benutzt.

## 5. Induktionsanwendungen nach Peano

Das erneut behandelte [Lemma `n+1≠1` bei 17284–17437](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17284), wiederholt ab 20483, ist unter der Kettengrundlage richtig: `W_A(n+1)` enthält mindestens zwei Grundblöcke und kann deshalb nicht die Kette `A=W_A(1)` sein. Der Text verwendet hier einen Grundfall und danach ein direktes allgemeines Argument; ein zusätzlicher Induktionsschritt ist dafür nicht erforderlich.

### Gleiche Ketten haben dieselbe Anzahl von Grundzeichen

**Fundstellen:** [17440–17628](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17440), wiederholt [20643 ff.](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:20643).

Der Aufbau des Beweises ist richtig, wenn eine feste Zerlegung in Grundzeichen gemeint ist. Die Induktionsaussage muss für **alle** Ketten der Länge `n` und ihre gleichen Gegenstücke gelten. Für `n+1` zerlegt man `A=aU`, `B=bV` mit je einem Grundzeichen vorn. Aus der rekursiven Gleichheitsdefinition folgen `a=b` und `U=V`; aus der Induktionsannahme hat `V` ebenso wie `U` die Länge `n`. Damit hat `B` die Länge `n+1`. Es geht nicht um die Länge der unterschiedlichen Namen eines Symbols: „Kuh“ als vereinbarter Block und seine drei Druckbuchstaben sind verschiedene Zerlegungsebenen.

### Äquivalenzrelation der Symbolgleichheit

**Fundstellen:** [17635–18313](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17635), wiederholt [20842 ff.](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:20842).

Reflexivität, Symmetrie und Transitivität lassen sich so auf die Grundgleichheit zurückführen. Deren entsprechende Eigenschaften müssen vorausgesetzt sein; der Fall „ein Grundzeichen“ beweist sie nicht aus dem Nichts. Im Symmetriebeweis folgt `A_n=B_n` [bei 17940–17944](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17940) aus der Gleichheitsdefinition und der Annahme `A=B`, nicht aus der Induktionsannahme über **Symmetrie**. Diese liefert anschliessend `B_n=A_n`. Für die einzelnen Anfangszeichen liefert der Grundfall `B_{n+1}=A_{n+1}`; der Index `n+1` ist hier ein Name des einzelnen Anfangszeichens, nicht dessen Länge. Die Parallelstellen sind 21147 und 21169.

Bei Transitivität ist der Schluss auf die beiden Restketten der Länge `n` mit der Induktionsannahme und auf die Grundzeichen mit dem Grundfall richtig. Der Satz über „höchstens n“ bei 18277 darf nicht als stillschweigende starke Induktionsannahme gelesen werden; gebraucht werden hier nur genau `n` und der bereits erledigte Grundfall 1.

Ein Grundlagenpunkt bleibt aus Arbeitspaket 2 bestehen: Mehrere frühere Beweise verwenden die Äquivalenz der Symbolgleichheit und verweisen dabei schon auf dieses spätere Induktionslemma. Der spätere Beweis kann deshalb nicht seinerseits die **einzige** Grundlage der zur Herleitung der Zahleninduktion verwendeten Gleichheit sein. Die frühe Begründung [ab 562](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:562) ist der passende Ort für die unabhängig benannte Kettengrundlage; der spätere Beweis kann dann eine erneute Induktionsübung sein. Die technische Bereinigung der Verweise bleibt Arbeitspaket 7.

### Transitivität der Zahlengleichheit

**Fundstellen:** [18333–18547](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18333), wiederholt [21544–21758](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:21544).

Der Satz ist richtig. Zu Beginn werden aber `a₁=a₂` und `a₁=a₃` angenommen; [18409](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18409) wird stattdessen `a₂=a₃` als Voraussetzung benutzt. Die Parallelstellen sind 21574 und 21620. Will man die übliche Transitivität zeigen, sollte man durchgehend `a₁=a₂` und `a₂=a₃` voraussetzen und `a₁=a₃` folgern. Will man die ursprüngliche Variante zeigen, muss der Übergang zu `a₂=a₃` eigens begründet werden.

Ein geschlossener direkter Beweis steht praktisch bereits zur Verfügung: `W_A(a₁)=W_A(a₂)` und `W_A(a₂)=W_A(a₃)` liefern durch die zuvor begründete Kettentransitivität `W_A(a₁)=W_A(a₃)`, also `a₁=a₃`. Die Zahleninduktion ist dafür unnötig. Der vorhandene Text nennt am Ende einen Induktionsschritt, ohne eine Induktionsannahme klar auszusprechen; zudem benutzt er Zahlengleichheiten bereits in Ketten. Soll ausdrücklich ein weiterer Induktionsbeweis stehen bleiben, muss dessen Induktionsaussage und jede verwendete Gleichheitsregel vorab feststehen. Der direkte Beweis vermeidet diese zusätzliche Abhängigkeit und entspricht dem früheren [Lemma ab 11542](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:11542).

### Starke Induktion: Der kleinste Fehler gehört nicht zu den bereits richtigen Fällen

**Fundstellen:** [18609–18792](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18609), wiederholt [21824 ff.](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:21824).

Die beabsichtigte Aussage ist richtig:

\[
\bigl(P(1)\land\forall n\in\mathbb N\,
  ((\forall m\in\mathbb N\,(m\le n\Rightarrow P(m)))\Rightarrow P(n+1))\bigr)
\Rightarrow\forall n\in\mathbb N\,P(n).
\]

Der allgemeine Schritt muss eine Voraussetzung sein, keine Behauptung, alle früheren Fälle seien ohne Bedingung bereits richtig. Im Beweis wählt man bei einer nichtleeren Gegenbeispielmenge deren Minimum `m₀`. Der Fall `m₀=1` widerspricht `P(1)`. Sonst gilt `m₀=m₁+1`. Wegen der Minimalität gilt `P(n)` für alle `n<m₀`, also für alle `n≤m₁`. Der allgemeine Schritt ergibt dann `P(m₀)`, den Widerspruch.

Bei [18752](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18752), wiederholt [21967](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:21967), steht dagegen `n≤m₀`. Das schliesst den gewählten Gegenbeispielfall selbst ein und ist an dieser Stelle falsch. Es muss `n<m₀` oder `n≤m₁` heissen. Die Bildung der Gegenbeispielmenge, das Minimum, der kleinere Vorgänger und klassische Logik sind dieselben Voraussetzungen wie beim früheren Induktionssatz.

## 6. Handschläge: Richtige Formel, örtliche Korrektur und benannte Voraussetzungen

**Fundstellen:** [18868–19217](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18868), wiederholt [22083 ff.](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22083).

Es wird vorausgesetzt, dass jedes Paar verschiedener Personen sich genau einmal begrüsst. Die erste Zählung zählt gerichtete Zuordnungen „Person → andere Person“. Davon gibt es `n(n−1)`; jeder tatsächliche Handschlag kommt genau zweimal vor. Das ist eine richtige Doppelzählung. Die Formulierung, so oft würden wirklich Hände geschüttelt, sollte als „so viele Zuordnungen wurden gezählt“ präzisiert werden, damit die anschliessende Halbierung verständlich ist.

Der zweite Beweis hat den richtigen Anfang bei `n=2` und die richtige Rekursion `H(n+1)=H(n)+n`. Induktion darf bei 2 beginnen: Entweder wird sie für diese Startzahl formuliert oder auf `P(k)=` „die Formel gilt für `k+1` Personen“ mit `k≥1` angewendet. Die Anwendung erfordert also keine Aufnahme von 0 in ℕ.

Die Gleichung [19118](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19118), wiederholt [22333](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22333), ist falsch: `n(n−1)/2=(n²−n)/2+n`. Schon `n=2` ergibt `1=3`. Links muss ebenfalls `+n` stehen. Der geschlossene Rechnungsteil lautet dann:

\[
\begin{aligned}
H(n+1)&=\frac{n(n-1)}2+n
       =\frac{n^2-n+2n}2
       =\frac{n(n+1)}2\\
      &=\frac{(n+1)((n+1)-1)}2.
\end{aligned}
\]

Der Text sagt [bei 19027–19028](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19027) ausdrücklich, dass die Rechenregeln hier noch nicht begründet werden. Das ist eine offene Ankündigung und kein heimlich geführter Beweis dieser Regeln. Fachlich vorausgesetzt werden Multiplikationskommutativität und Distributivität, `n²=n·n`, die hier positive Differenz `n−1` sowie Bruchrechnung in ℚ mit Nenner 2. Für das Ergebnis in ℕ muss zusätzlich gesagt werden: Von zwei aufeinanderfolgenden Zahlen ist genau eine gerade, also ist `n(n−1)` durch 2 teilbar. Das folgt aus der Zerlegung nach gerader/ungerader Zahl oder aus der Division mit Rest durch 2. Der Zählbeweis erklärt die Ganzzahligkeit ebenfalls durch die Paarung der gerichteten Zuordnungen.

Nach dieser örtlichen Korrektur tragen **beide** Lösungswege die Handschlagformel. Es ist nicht nötig, das Beispiel zu verwerfen.

## 7. Zahlbereiche: Präzise Einordnung und kleine Ersatzformulierungen

**Fundstelle:** [15645–16040](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15645).

Bei den üblichen Einbettungen gilt:

\[
\mathbb N\subsetneq\mathbb Z\subsetneq\mathbb Q
\subsetneq\mathbb R\subsetneq\mathbb C,
\qquad
\mathbb I:=\mathbb R\setminus\mathbb Q.
\]

`ℐ` ist hier nur eine erklärende Abkürzung für die irrationalen Zahlen. Es gilt `ℚ∩ℐ=∅` und `ℚ∪ℐ=ℝ`. Irrationale Zahlen bilden keine weitere Stufe zwischen ℚ und ℂ.

| Bereich | Passende Erklärung | Beispiel |
| --- | --- | --- |
| ℕ | Deine positiven Zählzahlen, beginnend bei 1 | `1, 2, 7` |
| ℤ | Positive und negative ganze Zahlen sowie 0 | `−4, 0, 7` |
| ℚ | Quotienten `z/n` mit `z∈ℤ`, `n∈ℕ` | `−3/2, 0/1, 7/1` |
| ℝ∖ℚ | Reelle Zahlen, die kein solcher Quotient sind | `√2` |
| ℝ | Rationale und irrationale Zahlen zusammen | `1, −3/2, √2` |
| ℂ | Zahlen `a+bi` mit `a,b∈ℝ`, wobei `i²=−1` | `1+0i, √2+0i, i` |

Die Definitionen und die Dezimalcharakterisierung sind mit [OpenStax, College Algebra 2e, Abschnitt 1.1](https://openstax.org/books/college-algebra-2e/pages/1-1-real-numbers-algebra-essentials) abgeglichen; die komplexen Zahlen mit [Abschnitt 2.4](https://openstax.org/books/college-algebra-2e/pages/2-4-complex-numbers). Die folgenden Gegenbeispiele und Reparaturbegründungen sind eigene Nachrechnungen am Manuskript.

- **Bei 15877–15879:** „als Folge von Ziffern darstellbar“ unterscheidet rationale Zahlen nicht von irrationalen. Falls eine endliche Dezimalschreibweise gemeint ist, wird umgekehrt `1/3` fälschlich ausgeschlossen. Passend ist: „Eine rationale Zahl lässt sich als Quotient zweier ganzer Zahlen mit Nenner ungleich null schreiben. Ihre Dezimaldarstellung endet oder wird schliesslich periodisch.“ Auch irrationale reelle Zahlen haben Dezimaldarstellungen; diese enden nicht und werden nicht schliesslich periodisch. Die Deutung des Wortes „rational“ aus seiner Wortgeschichte bleibt Arbeitspaket 6.
- **Bei 15933:** „Jede rationale Zahl ist eine irrationale Zahl“ ist falsch. `1=1/1` ist ein Gegenbeispiel. Kleinster Ersatz: „Keine rationale Zahl ist irrational. Rationale und irrationale Zahlen bilden zusammen die reellen Zahlen.“ Die richtigen Sätze „Jede natürliche Zahl ist ganz“ und „Jede ganze Zahl ist rational“ bleiben erhalten.
- **Bei 15925:** `√2` ist die Länge einer Diagonale eines **Einheitsquadrats**, allgemeiner das Verhältnis von Diagonale zu Seitenlänge eines Quadrats. Bei Seitenlänge `s>0` ist die Diagonale `s√2`; ohne Einheitswahl ist ihre Länge nicht stets √2.
- **Bei 15971:** Als Beispiel ist `i` eine **imaginäre**, nicht irrationale Zahl. Am klarsten: „Wir erweitern die reellen Zahlen um eine Zahl i mit i²=−1. Diese Zahl ist nicht reell.“ Für jede reelle Zahl `x` gilt `x²≥0`; deshalb kann keine rationale oder irrationale reelle Zahl ihr Quadrat gleich −1 haben. Im üblichen Gebrauch bezeichnet `√−1` den gewählten Wert `i`; die Gleichung `z²=−1` hat die beiden Lösungen `i` und `−i`.
- **Bei 15999–16006:** Dass keine irrationale Zahl gleich `i` ist, ist **richtig**, aber zu eng: Keine **reelle** Zahl ist gleich `i`. Auch „Jede irrationale Zahl ist eine komplexe Zahl“ ist bei der üblichen Einbettung `r↦r+0i` richtig. Das gilt ebenso für rationale Zahlen. Komplex bedeutet also nicht automatisch „nicht reell“. „Rein imaginär und von null verschieden“ bedeutet `bi` mit reellem `b≠0`; `1+i` ist komplex und nicht reell, aber nicht rein imaginär.

Die Dezimalcharakterisierung hat einen kurzen eigenen Grund: Bei der schriftlichen Division durch einen positiven Nenner `n` gibt es nur die Reste `0,…,n−1`. Ein Rest 0 beendet die Entwicklung; ein wiederholter Rest wiederholt die nachfolgenden Ziffern. Umgekehrt liefert ein periodischer Block durch Multiplikation mit der passenden Zehnerpotenz und Subtraktion einen Quotienten ganzer Zahlen. Das bekannte `0,999…=1` ist eine Doppeldarstellung derselben rationalen Zahl, kein Gegenbeispiel. Eine Darstellung als Dezimalentwicklung und eine endliche symbolische Bezeichnung wie `√2` sind verschiedene Dinge.

Die Zahlenbereichsübersicht darf vorläufig vertraute ganze, rationale und komplexe Zahlen beschreiben, ohne sie dort schon vollständig zu konstruieren. Dann muss dies als Überblick angekündigt sein. Ihre Rechengesetze sind damit noch nicht aus der Kettenkonstruktion bewiesen.

Die Grenzen [der vorzeichenbehafteten 32-Bit-Zahlen bei 16024–16036](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16024) stimmen für die Zweierkomplementdarstellung: `−2³¹=−2147483648` bis `2³¹−1=2147483647`. Diese Voraussetzung sollte genannt werden, weil „32 Bit“ allein die Vorzeicheninterpretation nicht festlegt. Es sind Werte aus einer endlichen Teilmenge von ℤ. Die vorzeichenlosen Werte wären `0,…,2³²−1`. Der endliche Bereich ist nicht unter der gewöhnlichen Addition abgeschlossen; ein festgelegtes Überlaufverhalten muss von der Rechnung in ℤ unterschieden werden.

## 8. Bruchrechnung, ggT, Euklid und kgV in den Restposten

### Das Bruchbeispiel rechnet im Wesentlichen richtig

**Fundstellen:** [Restposten 1024–1355](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:1024).

Beide Wege ergeben korrekt

\[
\frac{145}{45}-\frac{21}{15}
=\frac{1230}{675}=\frac{82}{45}=1{,}8\overline2.
\]

Auch `145/45=29/9`, `21/15=7/5` und die abschliessende Zerlegung `82/45=1+4/5+1/45` sind richtig. In [Zeile 1331](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:1331) steht aber zweimal `3³`, wo `3²` stehen muss:

\[
\frac{100}{45}=\frac{2^2 5^2}{3^2 5}
=\frac{2^2 5}{3^2}=\frac{20}{9}=2+\frac29.
\]

Mit `3³` wären die beiden mittleren Brüche `20/27`, nicht `20/9`. Die Endwerte des Beispiels werden dadurch nicht falsch. Die gerundete Gegenrechnung `≈1,82` ist eine nützliche Plausibilitätskontrolle, kein Ersatz für die exakte Rechnung.

### Gemeinsamer Teiler und Existenz des ggT

Die [erste Erklärung bei 908–947](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:908) schliesst `t=1` aus; die [formale ggT-Definition bei 1360–1370](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:1360) lässt 1 dagegen richtig zu. „Gemeinsamer Teiler“ kann absichtlich anders eingeschränkt werden, aber dann muss die erste Bezeichnung **nichttrivialer gemeinsamer Teiler** lauten. Für gewöhnliche Teilbarkeit wird 1 zugelassen. „Teilerfremd“ heisst: kein gemeinsamer positiver Teiler grösser als 1; äquivalent `gcd(a,b)=1`, nicht „überhaupt kein gemeinsamer Teiler“.

Für positive `a,b` ist `D={d∈ℕ | d teilt a und b}` nichtleer, weil `1∈D`, und liegt in `{1,…,min(a,b)}`. Es besitzt daher ein Maximum. Das schliesst die Existenzlücke der Definition, ohne die Primfaktorzerlegung vorwegzunehmen. Für negative Eingaben nimmt man die Beträge. Der anfangs ausgeschlossene Fall Zähler 0 beim Bruchkürzen kann gesondert durch `0/n=0/1` erledigt werden.

Ist `g=gcd(a,b)` und hätte `a/g,b/g` einen gemeinsamen Teiler `h>1`, wäre `hg` ein gemeinsamer Teiler von `a,b`, grösser als `g`. Das widerspricht der Maximalität. Der Text hat diesen passenden Ansatz [bei 1585–1615](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:1585) bereits. Nur „wäre der grösste gemeinsame Teiler“ ist dort zu stark: „wäre ein grösserer gemeinsamer Teiler“ genügt. Dieses Argument begründet die später benötigte gekürzte Bruchdarstellung. Für `z∈ℤ`, `n∈ℕ`, `z≠0` wendet man es auf `|z|,n` an und erhält `z/n=(z/g)/(n/g)` mit teilerfremden Zähler und Nenner.

### Primfaktorformeln: Richtige Ziele, fehlerhafte Zwischenzeilen

**Fundstellen:** [ggT ab 1481](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:1481), [kgV ab 3542](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:3542), [Zusammenhang ab 4031](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:4031).

Hier wird die Existenz und Eindeutigkeit der Primfaktorzerlegung bereits vorausgesetzt. Man muss entweder diesen Satz vorher beweisen oder die Voraussetzung ausdrücklich nennen. Wähle eine Aufzählung `p₁=2,p₂=3,…` aller Primzahlen ohne Wiederholungen und schreibe `a=∏ₖ pₖ^{αₖ}`, `b=∏ₖ pₖ^{βₖ}`, wobei die Exponenten in `ℕ₀` liegen und nur endlich viele ungleich 0 sind. Das Produkt mit lauter Exponenten 0 hat den Wert 1.

Dann gilt für positive ganze Zahlen: `d` teilt `a` genau dann, wenn jeder Primexponent von `d` höchstens dem entsprechenden von `a` ist. Damit folgen direkt

\[
\gcd(a,b)=\prod_kp_k^{\min(\alpha_k,\beta_k)},
\qquad
\operatorname{lcm}(a,b)=\prod_kp_k^{\max(\alpha_k,\beta_k)}.
\]

Das erste Produkt ist gemeinsamer Teiler und jeder gemeinsame Teiler teilt es. Das zweite ist gemeinsames Vielfaches und teilt jedes gemeinsame Vielfache; positive Teilbarkeit impliziert die entsprechende Grössenordnung. Das beweist auch die Maximalität bzw. Minimalität. Aus `min(α,β)+max(α,β)=α+β` ergibt sich `gcd(a,b)·lcm(a,b)=ab`. Der zweifällige Beweis dieser Min/Max-Summe [bei 3946–4018](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:3946) stimmt.

Die ausgeschriebenen längeren Beweise enthalten dagegen zusätzliche örtliche Fehler:

- Bei [1648–1683](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:1648), ebenso 1732–1767, müssen am ausgezeichneten Primfaktor sämtliche Exponenten bei `k₀` ausgewertet sein; dort stehen teilweise freie `k`. Bei 1675/1759 wird zudem das abgezogene `ρ` durch `m` ersetzt.
- In [1902–1913](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:1902), entsprechend 1974–1985, wird `ν=min(l₁(k₁),l₂(k₁))` eingesetzt, wo der Exponent `l₁(k₁)−l₃(k₁)` beziehungsweise `l₂(k₁)−l₃(k₁)` benötigt wird. `l₁(k₁)−ν<0` kann gerade **nicht** gelten, weil `ν≤l₁(k₁)`. Das ist ein tatsächlicher Beweisfehler, keine neue Konvention.
- Bei [2099](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:2099) muss das zweite Produkt `n₂` ergeben, nicht `n₁`.
- Im kgV-Abschnitt wird [ab 3549](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:3549) über `k∈ℙ` statt über die Indizes `k∈ℕ` der Primzahlen multipliziert. Unter der genannten Aufzählung wäre etwa der Faktor `p₁=2` ausgelassen. Entweder über alle Primzahlen `p` mit Exponenten `v_p(a)` oder über alle Indizes `k` mit `pₖ` laufen lassen, nicht beide Schreibweisen mischen.
- Bei [3785](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:3785) muss im Fall `l₄(k)>0`, also `l₁(k)>l₂(k)`, die Differenz `l₁(k)−l₁(k)=0` stehen. Die gedruckte Differenz `l₂(k)−l₁(k)` ist dann negativ. In [3928](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:3928) muss der Exponent des kgV, `l₅(k)`, mit dem Maximum verglichen werden; `l₄(k₁)` ist der falsche Exponent und verwendet den falschen Index. Beispielsweise bei `a=b=2` ist `l₄(1)=0`, das betreffende Maximum aber 1.

Die kgV-Existenz [bei 3487–3527](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:3487) ist unter den hergeleiteten Rechengesetzen richtig: `ab=ba` ist ein gemeinsames positives Vielfaches; der Minimumsatz liefert das kleinste. Bei 4092 ist die Produktklammerung als `∏ₖ(pₖ^{αₖ}pₖ^{βₖ})` zu schreiben, damit beide Vorkommen von `k` gebunden sind. Der Zusammenhangssatz selbst bleibt richtig.

### Euklid: Invariante und Terminierung sind zwei Teile

**Fundstellen:** [Algorithmus 2149–2217](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:2149), [Beweis bis 2831](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:2221).

Das Verfahren ist richtig: Beginne mit `a=max(n₁,n₂)`, `b=min(n₁,n₂)`, beide positiv; bestimme den Rest `r` mit `a=qb+r`, `0≤r<b`. Ist `r=0`, gib `b` zurück; andernfalls ersetze `(a,b)` durch `(b,r)`.

Bei [2196](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:2196) muss das Ergebnis als `gcd(n₁,n₂)` der **ursprünglichen Eingaben** bezeichnet werden, nicht als `gcd(n₁,n₃)` mit dem veränderlichen Zwischenwert. Ein Gegenbeispiel bereits am ersten Stopp ist `(n₁,n₂)=(4,2)`: `n₃=4`, also würde die gedruckte Bezeichnung `gcd(4,4)=4` statt 2 behaupten. Die Invariante ist der ggT des jeweils aktuellen **Paares**, nicht der einer ursprünglichen Eingabe mit einem beliebigen Zwischenwert.

Bei [2282](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:2282) steht `gcd(n₁,n₁)=0`; das ist falsch, etwa für `n₁=2`. Der **Rest** ist 0, der zurückzugebende ggT ist `n₁`. Bei [2313](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:2313) ist das zweite Minimum `min(l₂(k),l₁(k))`, nicht `min(l₂(k),l₂(k))`. Bei 2503 muss `n₁≥n₂` die folgende Quotientenabschätzung begründen, nicht `n₁≥n₁`.

Der lange Rest-Beweis verfolgt die passende Invariante. Kurz geschlossen wird er so: Für jeden positiven Teiler `d` gilt `d|a` und `d|b` genau dann, wenn `d|b` und `d|r`, weil `r=a−qb` und `a=qb+r`. Damit stimmen die Mengen der gemeinsamen Teiler und ihre Maxima überein. Im Nullrestfall sind die gemeinsamen Teiler von `a,b` genau die Teiler von `b`, also ist `b` das Ergebnis; `gcd(b,0)` muss dafür nicht neu definiert werden.

**Was noch fehlt:** Nach jedem fortgesetzten Schritt ist die neue zweite Zahl `r` positiv und strikt kleiner als die vorherige zweite Zahl `b`. Eine unendliche solche Abstiegskette in ℕ gibt es nach dem reparierten Minimumsatz nicht. Deshalb endet der Algorithmus. Die Invariante allein würde noch nicht beweisen, dass er jemals ein Ergebnis ausgibt. Die Existenz des Restes und `0≤r<b` sind ebenfalls vorauszusetzen oder als Division-mit-Rest-Satz zu beweisen; die Formel mit `floor(a/b)` allein ersetzt diesen Nachweis nicht.

### Weitere eindeutige Rechenfehler im selben Abschnitt

Die Min/Max-Definitionen und ihre Indikatorformeln [bei 2855–2912](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:2855) stimmen, wobei `δ_P` genau 1 für wahres `P` und sonst 0 sei. In [2954](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:2954) muss `x·0+y·1=y` statt `=1` stehen; in [2962](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:2962) `y·0+x·1=x` statt `=y`. Für `x=3,y=2` erhält man so korrekt Minimum 2 und Maximum 3. In [3383](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:3383) ist ein Summand `xδ_{−x≥−y}` verdoppelt; streicht man das zusätzliche Vorkommen, stimmt die folgende Rechnung. Die symmetrischen Min/Max-Formeln und die beiden Negationsidentitäten selbst sind richtig.

Die Prozentaufgabe [ab 4109](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:4109) liefert richtig `b=a/(1−a/100)` und `b/a=1/(1−a/100)`, sofern der Ausgangswert `t₀>0` und `0<a<100` sind. Im Beispiel `k=4`, Verlust 75 %, müssen [bei 4238](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:4238) **300 %** statt 400 % stehen: Der neue Wert 25 wächst um 75 auf 100. Die Herleitung `(k−1)·100` ist richtig, nur der eingesetzte Endwert falsch. `1/k` bei 4166 ist ein **Anteil**, der Prozentsatz lautet `100/k`. Anfänglich ist der alte Wert einheitlich `t₀`, der neue `t₁` zu nennen. Bei Verlust 0 ist `b=0`, aber `b/a` undefiniert; bei Verlust 100 % gibt es keinen endlichen prozentualen Anstieg vom Wert 0 zurück zum positiven Ausgangswert. Diese Bedingungen erklären genau die Nenner beim Kürzen.

## 9. √2 in den Restposten: Der Widerspruchsbeweis lässt sich schliessen

**Fundstellen:** [Paritätslemma 27153–27284](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27153), [Irrationalitätsbeweis 27294–27684](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27294).

Das Paritätslemma beginnt mit `z₁²=2z₂`. Der sprachliche Schluss lautet [bei 27175](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27175), `z₂` sei gerade; später wird das Lemma für die Geradheit von **z₁** gebraucht. Die gedruckte Aussage über `z₂` ist dabei **nicht falsch**: Aus `z₁=2k` folgt tatsächlich `z₂=2k²`. Der ausgeschriebene Beweis zeigt zunächst, dass eine ungerade Zahl ein ungerades Quadrat besitzt, und behandelt danach die andere Richtung „gerade Zahl → gerades Quadrat“. Für die Aussage über `z₂` fehlt am Ende die ausdrückliche Kürzung. Am zweckmässigsten lautet das benötigte Lemma: „Ist das Quadrat einer ganzen Zahl gerade, dann ist die Zahl selbst gerade.“ Die korrekte Ausmultiplizierung `(2k+1)²=2(2k²+2k)+1` beweist es durch Kontraposition; vorausgesetzt ist, dass jede ganze Zahl entweder gerade oder ungerade ist und nicht beides.

Im nachfolgenden Beweis gibt es weitere örtliche Punkte:

- Bei [27317](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27317) muss der Bereich `q∈ℚ` stehen. Ohne diesen Bereich wäre „Es gibt kein q mit q²=2“ über ℝ gerade falsch.
- Das Paar schreibt man `(n₁,d₁)∈ℤ×ℕ`, nicht als Element von `(ℤ,ℕ)`. Der Nenner heisst bei 27375 irrtümlich `n₂` statt `d₁`.
- Bei [27418](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27418) ist die Kürzungsrichtung falsch: Gemeinsam durch 2 teilbar bedeutet `n₁=2n₂` und **`d₁=2d₂`**, nicht `d₂=2d₁`. Genau die korrigierte Richtung wird in der nächsten Bruchgleichung benötigt.
- Wird `n₁∈ℤ` zugelassen, ist die Hälfte eines geraden `n₁` nicht notwendig natürlich, wie [27517](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27517) behauptet. Man kann entweder `n₃∈ℤ` zulassen oder wegen `q²=|q|²` von Anfang an mit positivem Zähler arbeiten. Die Gleichung `q²=2` schliesst den Zähler 0 aus.
- Der Verweis zur gekürzten Bruchdarstellung ist noch ein Platzhalter. Der ggT-Ansatz aus Abschnitt 8 dieser Notiz liefert die fehlende Voraussetzung. Symmetrie der Gleichheit ist bei 27545 das gemeinte Wort; „kommutativ“ ist hier keine zusätzliche Rechenregel.

**Geschlossener Ersatzbeweis:** Angenommen, eine rationale Zahl habe Quadrat 2. Durch Übergang zum Betrag und Kürzen kann man sie als `p/q` mit positiven teilerfremden `p,q` schreiben. Dann `p²=2q²`. Nach dem Paritätslemma ist `p=2k`. Einsetzen und Kürzen des von null verschiedenen Faktors 2 ergibt `q²=2k²`. Also ist auch `q` gerade. Damit besitzen `p,q` den gemeinsamen Teiler 2, im Widerspruch zur gekürzten Darstellung. Folglich gibt es kein rationales `r` mit `r²=2`.

Damit ist die Nichtexistenz einer **rationalen** Lösung bewiesen. Dass es eine positive **reelle** Lösung gibt, folgt erst aus einer Grundlage der reellen Zahlen, etwa Vollständigkeit und einem daraus bewiesenen Wurzelsatz. Die geometrische Veranschaulichung benutzt ihrerseits ausdrücklich vorausgesetzte Geometrie. Sie darf erläutern, warum eine Erweiterung sinnvoll ist, ersetzt aber nicht unbemerkt die Konstruktion oder Existenzbegründung für ℝ.

Bei [27691](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27691) ist die Behauptung über die nicht rationale Diagonallänge eines beliebigen Quadrats zu weit. Ein Quadrat der Seitenlänge `1/√2` hat Diagonallänge 1. Irrational ist stets das **Verhältnis** Diagonale/Seitenlänge; beim Einheitsquadrat also die Diagonallänge. Die spätere Rechnung [27798–27836](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27798) verwendet dieses Verhältnis richtig und nennt auch die positive Seitenlänge vor der Division.

Auch [27940–27942](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27940) ist wörtlich falsch: Eine Zahl, deren Quadrat exakt 2 ist, lässt sich beispielsweise **exakt als √2 bezeichnen**. Was unmöglich ist, ist ihre Darstellung als Quotient ganzer Zahlen oder als endliche beziehungsweise schliesslich periodische Dezimalentwicklung. Die geplante Annäherung durch rationale Zahlen passt danach weiterhin. Schnitte, Cauchyfolgen modulo Nullfolgen und geeignete Intervallschachtelungen sind mögliche Konstruktionen; ihre Gleichwertigkeit verlangt genaue Definitionen und Beweise. Beliebige Folgen oder beliebige Intervalle leisten dies nicht. Die folgenden Konvergenzbeweise sind hier nicht vollständig geprüft.

## 10. Ergänzung zur Zuordnung von Zahlen und Anfangsstückmengen

**Fundstellen:** [13120–13868](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:13120). Dieser in Arbeitspaket 2 ausdrücklich ausgeklammerte Einschub steht unmittelbar vor der Addition. Bei der jetzigen Prüfung wurden folgende konkrete Stellen mit erfasst:

| Stelle | Befund und örtliche Korrektur |
| --- | --- |
| 13341 | Es wird `n₄` quantifiziert, aber `n₃` im Reststück benutzt. Dort muss derselbe gebundene Restindex `n₄` stehen. |
| 13403 | Im Fall `B W_A(n₄)=W_A(n₁)` wird zusätzlich `B=W_A(n₁)` und später `B C=W_A(n₁)W_A(n₄)W_A(n₃)` geschrieben. Beides passt nicht zur Voraussetzung. Richtig ist `B C=B W_A(n₄)W_A(n₃)=W_A(n₁)W_A(n₃)=W_A(n₂)`, mit `C=W_A(n₄)W_A(n₃)`, und daher `B≠W_A(n₂)` wegen echter Verlängerung. |
| 13482 | Die Umkehrabbildung nimmt `E_n` entgegen: `g(E_n)=n`, nicht `f(E(n))↦n`. Ihre Wohldefiniertheit ist die vorher zu beweisende Eindeutigkeit des Index. |
| 13649 | In `E₇` steht zuletzt eine Kette aus acht statt sieben `A`. Es muss die Kette aus sieben `A` sein. Die Anzahl der aufgelisteten Elemente allein bemerkt diesen Abschreibfehler nicht. |
| 13684 | Im zweiten Inklusionsglied steht `M_{n₁}` statt `E_{n₁}`. |
| 13753 | Zwischen den beiden Mengen steht `∨` statt der Mengenvereinigung `∪`. |
| 13803 | Rechts wird `|E_{n₁}|≤|E_{n₁}|` verglichen. Das ist immer wahr und kann nicht gleichbedeutend mit `n₁≤n₂` sein; etwa `n₁=2,n₂=1` widerlegt die behauptete Äquivalenz. Rechts muss `|E_{n₁}|≤|E_{n₂}|` stehen; der Beweis ist an dieser Stelle zudem noch nicht fertig ausgeschrieben. |

Die eigentliche Konstruktion trägt unter der bisherigen Grundlage: `E_n={W_A(k) | 1≤k≤n}`. Für `a<b` gehört `W_A(b)` zu `E_b`, wegen Injektivität der Kettenbenennung aber nicht zu `E_a`. Deshalb sind die `E_n` verschieden und `n↦E_n` ist bijektiv auf die Menge aller solchen `E_n`. Für `a≤b` ist `E_a⊆E_b`; umgekehrt würde bei `a>b` das Element `W_A(a)` die Inklusion widerlegen. Also `a≤b` genau dann, wenn `E_a⊆E_b`.

Für den anschliessenden Schritt zur Mächtigkeit ist ausdrücklich die Bijektion `k↦W_A(k)` von `{1,…,n}` auf `E_n` anzugeben. Damit hat `E_n` genau `n` Elemente und die korrigierte Mächtigkeitsformel folgt. Das verwendet bereits die Zahlen bzw. den Begriff einer endlichen Anzahl; es ist eine Übersetzung der Kettenzahlen in endliche Mächtigkeiten, keine davon unabhängige erstmalige Konstruktion der natürlichen Zahlen. Eine vollständige zusätzliche Prüfung der allgemeinen Mächtigkeitstheorie ist damit nicht behauptet.

## 11. Kleinstes zusammenhängendes Reparaturpaket und Kontrolle

1. Die bereits dokumentierte Kettengrundlage beibehalten und bei der Addition Existenz und Eindeutigkeit aussprechen. Zahlengleichheit, Einsetzen und Kürzen auseinanderhalten.
2. Im Nachfolger-/Assoziativitätsbeweis die richtige Begründung nennen und im direkten Beweis die zwei verschiedenen Gruppierungen in die Schlusszeile setzen. Den Kommutativitätsbeweis mit einem der beiden geschlossenen Wege aus Abschnitt 3 reparieren.
3. Die Multiplikationsrekursion beibehalten, ihre Existenzgrundlage benennen und die anschliessend verwendeten Rechengesetze in einer geordneten Beweiskette ergänzen. Subtraktion, Division und Potenzen entweder vorher einführen oder im Handschlagbeispiel ausdrücklich als vertraute vorläufige Rechenmittel kennzeichnen.
4. Bei den Induktionsübungen die Aussage samt Parametern nennen; im starken Induktionsbeweis die Grenze des schon bewiesenen Bereichs korrigieren. Die Grundgleichheit der Zeichen nicht erst aus der damit zuvor begründeten Zahleninduktion gewinnen.
5. Im Handschlagbeweis den verlorenen Summanden ergänzen, die Startzahl 2 und die Ganzzahligkeit der Halbierung erklären. Die zwei richtigen Lösungsansätze erhalten.
6. Die Zahlbereichsübersicht anhand von ℕ, ℤ, ℚ, ℝ und ℂ berichtigen; irrational und imaginär unterscheiden. Einheitswahl und exakte Bezeichnung gegenüber Dezimalentwicklung präzisieren.
7. Bei ggT/kgV 1 als Teiler zulassen, die Existenz begründen, die Primfaktorgrundlage ausdrücklich voraussetzen oder vorher beweisen und die Indizes vereinheitlichen. Euklid um die Terminierung ergänzen; die Rückgabe im Nullrestfall und die örtlichen Zahlenfehler korrigieren.
8. Beim √2-Beweis Paritätslemma, Kürzungsrichtung, Vorzeichen und Quantorenbereich korrigieren; die gekürzte Darstellung mit dem ggT-Argument rechtfertigen. Die Nichtexistenz einer rationalen Lösung von der Existenz einer reellen Lösung unterscheiden. Die erfassten Fehler bei den Anfangsstückmengen örtlich berichtigen.

Die Ersatzbehauptungen sind oben allgemein begründet; zu den zentralen falschen Formeln stehen Gegenbeispiele. Ergänzend wurden mit Python geprüft: 8000 Additionstripel mit Werten 1–20; 1728 Multiplikationstripel mit Werten 1–12 für die rekursiv berechnete Multiplikation und ihre Gesetze; 99 Handschlagfälle für 2–100 Personen; 1600 ggT/kgV-Paare mit positiven Eingaben 1–40 einschliesslich direkter Teiler-/Vielfachenbestimmung, Primexponentenformeln, Bruchkürzung und Euklid; 121 Min/Max-Paare aus −5 bis 5; 99 Prozentfälle für Verluste 1–99 %; die Parität von 201 ganzen Zahlen aus −100 bis 100 sowie 20 Anfangsstückmengen. Die Bruchrechnung und wesentliche numerische Gegenbeispiele wurden mit exakten rationalen Zahlen kontrolliert. Diese endlichen Kontrollen ergänzen die Begründungen und ersetzen weder allgemeine Beweise noch eine formale Lean-Prüfung. Insbesondere wird die Irrationalität von √2 durch den allgemeinen Widerspruchsbeweis, nicht durch eine endliche Suche belegt.

**Arbeitspaket 5 ist damit als dokumentierte fachliche Prüfung abgeschlossen.** Die Übernahme der Reparaturvorschläge ins Manuskript bleibt ein eigener Schritt. Die nächste nummerierte Aufgabe ist Arbeitspaket 6 zu erheblichen Sachbehauptungen ausserhalb der Kernmathematik.
