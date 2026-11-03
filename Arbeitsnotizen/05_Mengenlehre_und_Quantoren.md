# Tragende Definitionen der Mengenlehre und Quantoren

Stand: 3. November 2026. Ergebnis von Arbeitspaket 4 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Grundlage sind die durch `EinfuehrungMathe.lyx` eingebundenen aktuellen LyX-Quellen. Zeilenangaben beziehen sich auf diese Quellen, nicht auf Buchseiten oder ältere TeX-Exporte. Die Prüfung steht neben dem Manuskript; Manuskript, PDF und Sicherungen wurden nicht verändert.

## 1. Ergebnis und Reichweite

**Die Übertragung aussagenlogischer Regeln auf Mengenoperationen ist ein brauchbarer Weg. Sie benötigt zusätzlich Regeln für Quantoren, eine festgelegte Elementgleichheit und die Voraussetzung, dass die betrachteten Mengen existieren.** Im Text fehlen insbesondere die Bindung von Variablen und die ausdrückliche Unterscheidung zwischen einer Formel für ein einzelnes Element und einer Behauptung über alle Elemente.

Die Fehler aus B6–B8 der [ersten Befunde](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/02_Erste_Befunde.md) bestätigen sich. Darüber hinaus treten tatsächliche Folgefehler auf: zusätzliche Verneinungen im Beweis über die symmetrische Differenz, ein falscher Vereinigungsschritt bei Teilmengen und vertauschte Variablenbereiche bei der Linkseindeutigkeit. Andere Sätze bleiben richtig, obwohl ihre ausgeschriebenen Beweise repariert werden müssen.

| Gegenstand | Einordnung | Folge |
| --- | --- | --- |
| Existenz- und Allquantor als blosse Konjunktion bzw. Implikation | Falsche formale Äquivalenzen | Die Quantoren dürfen beim Umformen nicht verschwinden. Der Fehler steht bereits im Logikteil. |
| „Genau ein“ | Falsche Formel; sprachliche Erklärung trifft die Absicht | Ein Zeuge und eine allgemeine Eindeutigkeitsbedingung müssen gemeinsam gebunden werden. |
| Teilmenge und Mengengleichheit | Unvollständige formale Darstellung, sofern keine allgemeine Lesekonvention gilt | „Für jedes Element“ ergänzen; ein einziges geprüftes Element genügt nicht. |
| Mengendifferenz | Widersprechende Definitionen | Reihenfolge und Konjunktion berichtigen; spätere Verwendungen einzeln unterscheiden. |
| Leere Menge | Brauchbare Konstruktion; Lücke im Unabhängigkeitsbeweis | Zwei verschiedene Hilfsmengen vergleichen; Reflexivität allein zeigt keine Eindeutigkeit. |
| Einzelmengen, Potenzmenge, echte Teilmenge | Im Kern passende Definitionen | Elementgleichheit, Existenzvoraussetzungen und Geltungsbereiche ausdrücklich festhalten. |
| Ungewöhnliche Namen und Einschränkungen | Eigene Begriffsentscheidungen | `⊂` für nicht notwendig echte Inklusion, „identitiv“ und die Beschränkung auf nichtleere Relationen sind nicht allein deshalb falsch. |

Geprüft sind die genannten Grunddefinitionen, die beiden Quantorenkapitel und die unmittelbar einschlägigen Anwendungen auf Gleichheit, leere Menge, symmetrische Differenz, Teilmengen und Ersetzung. Zur Verfolgung der Folgen wurden ausserdem Relations- und Partitionsdefinitionen sowie eine spätere Anwendung der Quantorennegation herangezogen. **Dies ist keine vollständige Einzelprüfung aller Beweise über Funktionen, Mächtigkeiten, Folgen oder aller Wahrheitstafeln.** Die Arithmetik bleibt Arbeitspaket 5. Die Unterscheidungen aus [Arbeitspaket 3](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/04_Aussagenbegriff_und_Widerspruchsfreiheit.md) zwischen Formel, Wahrheit und angenommener Voraussetzung gelten hier weiter.

## 2. Was bei Variablen zusätzlich feststehen muss

**Fundstellen:** [Variablen als Metasymbole, Symbolteil 3169](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:3169); [lokale Variablen 3505](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:3505); [Quantoreneinführung im Logikteil 25820](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:25820).

Die bisherigen Erklärungen über Namen und lokale Variablen ersetzen noch keine Festlegung der Quantorenbindung. Eine kleine Ergänzung reicht für die anschliessenden Beweise:

- In `x=1` ist `x` frei. Ob die Formel wahr ist, hängt von der Belegung von `x` ab. Die Formel ist weder sinnlos noch bereits eine Aussage darüber, dass jedes oder irgendein Objekt gleich 1 sei.
- In `∃x∈M (x=1)` ist dieses Vorkommen von `x` gebunden. Gefragt wird, ob die Menge einen passenden Zeugen enthält. `M` bleibt ein Parameter.
- In `(x∈M) ∧ (∀x∈M A(x))` ist das erste `x` frei und das `x` innerhalb des zweiten Konjunkts gebunden. Gleiche Buchstaben erzeugen über getrennte Geltungsbereiche hinweg keine Bindung. Klarer: `(a∈M) ∧ (∀x∈M A(x))`.
- Bei `∀x∈M A(x)` bedeutet `A(x)` eine Formel mit gegebenenfalls freiem `x`, nicht notwendig einen schon vollständig bestimmten Satz. Weitere Parameter dürfen vorkommen; deren Belegung bleibt während des Schlusses fest.

Die gebundene Variable kann umbenannt werden, wenn die zugehörigen Vorkommen mit umbenannt werden und keine andere Variable versehentlich gebunden wird. So sind `∀x∈M (x=1)` und `∀z∈M (z=1)` gleichbedeutend. Dagegen darf aus `∀x∈M ∃y∈M (x≠y)` nicht `∀y∈M ∃y∈M (y≠y)` werden. Für `M={1,2}` ist die erste Formel wahr und die zweite falsch. Die innere Bindung hat die ursprünglich äussere Variable eingefangen. Mit einem frischen Namen `z` tritt das Problem nicht auf.

**Örtlicher Ergänzungsvorschlag:** „Ein Quantor bindet die angegebene Variable nur in dem Ausdruck, auf den er sich bezieht. Wir kennzeichnen diesen Bereich nötigenfalls mit Klammern. Beim Einsetzen und Umbenennen beachten wir, welche Vorkommen frei und welche bereits gebunden sind.“ Dies ergänzt die eigene Metasymbolsprache, ohne sie zu ersetzen. Für die Standardbegriffe siehe [forall x: Calgary, Abschnitt 27.3](https://forallx.openlogicproject.org/html/Ch27.html) und zur Unterscheidung freier und bereits gebundener Vorkommen bei der Einsetzung [Kapitel 31](https://forallx.openlogicproject.org/html/Ch31.html). Die Gegenbeispiele und ihre Anwendung auf das Manuskript sind eigene Nachrechnungen.

## 3. Existenz, Allgemeinheit und Eindeutigkeit

### Der Bindungsfehler steht an zwei Einführungsstellen

**Fundstellen:** [Allquantor im Logikteil, Formel 25865](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:25865), [Existenzquantor 25946](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:25946); [gemeinsame Definition im Mengenteil, Formeln 13009–13012](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13009).

Beide Stellen setzen sinngemäss

\[
(\exists x\in M:A)\ \leftrightarrow_{\rm def}\ (x\in M\land A),
\qquad
(\forall x\in M:A)\ \leftrightarrow_{\rm def}\ (x\in M\Rightarrow A).
\]

**Als formale Äquivalenzen sind diese Zeilen falsch.** Mit `M={1,2}` und `A(x)` gleich `x=1` ergibt sich:

| Vergleich | Quantifizierte Seite | Nicht quantifizierte Seite |
| --- | --- | --- |
| Existenz; freie Belegung rechts `x=2` | `∃x∈M (x=1)` ist wahr | `2∈M ∧ 2=1` ist falsch |
| Allgemeinheit; freie Belegung rechts `x=1` | `∀x∈M (x=1)` ist falsch | `1∈M ⇒ 1=1` ist wahr |

Auch die stillschweigende allgemeine Schliessung der ganzen Existenz-Äquivalenz hilft nicht: Sie würde ihre Gültigkeit für jede Belegung von `x` verlangen und scheitert am ersten Gegenbeispiel. Für den Allquantor kann man hingegen die **ganze rechte Seite quantifizieren**; das ist bereits die nötige Reparatur.

Bei vorausgesetzten unbeschränkten Quantoren lauten die Abkürzungen:

\[
\begin{aligned}
\exists x\in M\,A(x)&\;\leftrightarrow_{\rm def}\;
  \exists x\,(x\in M\land A(x)),\\
\forall x\in M\,A(x)&\;\leftrightarrow_{\rm def}\;
  \forall x\,(x\in M\Rightarrow A(x)),\\
\nexists x\in M\,A(x)&\;\leftrightarrow_{\rm def}\;
  \neg\exists x\in M\,A(x).
\end{aligned}
\]

Der Bereich der unbeschränkten Quantoren ist dabei festgelegt und umfasst die möglichen Elemente der betrachteten Mengen. Die gebundene Variable soll nicht zugleich frei in ihrer Bereichsangabe `M` vorkommen; für einen von einem Parameter abhängigen Bereich wählt man verschiedene Namen.

Die dritte Zeile des obigen Ersatzblocks ist bereits die richtige Absicht der zweiten Manuskriptzeile. **Quantoren werden so nicht aus aussagenlogischen Verknüpfungen hergeleitet.** Entweder erhalten die unbeschränkten Quantoren zuvor ihre Bedeutung, oder man führt direkt die beschränkten Quantoren sprachlich ein: Existenz ist wahr, wenn mindestens ein Element die Eigenschaft erfüllt; Allgemeinheit ist wahr, wenn jedes Element sie erfüllt. Ein Quantor ist deshalb keine Mengenbezeichnung, wie [im Logikteil um 26015](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:26015) vermutet wird, sondern ein Operator zur Bildung einer quantifizierten Formel. Die üblichen Abkürzungen sind auch in [Mathematics in Lean, Abschnitt 4.1](https://leanprover-community.github.io/mathematics_in_lean/C04_Sets_and_Functions.html#sets) beschrieben.

### „Genau ein“ braucht ein „für alle weiteren“

In [Zeile 13011](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13011) steht:

\[
(\exists!x\in M:A)\ \leftrightarrow_{\rm def}\
(\exists x\in M:A)\land(\exists y\in M:A\Rightarrow x=y).
\]

Der erste Quantor bindet `x` nicht im zweiten Konjunkt. Zudem prüft `∃y` nur einen möglichen Kandidaten, statt alle Kandidaten zu vergleichen. Die Abhängigkeit von `A` wird nicht angepasst. Selbst bei der wohlwollenden Lesart `A(y)` im zweiten Konjunkt bleibt die Formel falsch: Für `M={1,2}`, `A(t)` gleich `t=t` und die freie Belegung `x=1` ist die rechte Seite wahr, weil man `y=1` wählen kann. Links gibt es zwei Zeugen, also keinen eindeutigen.

Eine passende Ersatzformel ist:

\[
\exists!x\in M\,A(x)
\quad\leftrightarrow_{\rm def}\quad
\exists x\in M\;\bigl(A(x)\land
  \forall y\in M\,(A(y)\Rightarrow y=x)\bigr).
\]

Hier bleibt der Existenzzeuge `x` im Geltungsbereich seiner Bindung. Der sprachliche Text [13185–13224](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13185) beschreibt diese Absicht bereits gut. „Höchstens ein“ allein wäre `∀x,y∈M ((A(x)∧A(y))⇒x=y)`; es schliesst den Fall ohne Zeugen ein. Das Beispiel [13850](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13850), `∃!n∈ℕ (n·n=4)`, ist für die positiven natürlichen Zahlen richtig. Die spätere Funktionsdefinition benötigt Eindeutigkeit in genau diesem allgemeinen Sinn, nicht nur die Existenz eines passenden Vergleichskandidaten.

Auch die Frage nach „genau vier“ [13225–13248](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13225) kann beantwortet werden: Man fordert vier paarweise verschiedene Zeugen mit der Eigenschaft und zusätzlich, dass jeder weitere Zeuge einer dieser vier ist. Ein eigenes neues Quantorzeichen ist dazu nicht nötig. Standardformulierungen für „mindestens“, „höchstens“ und „genau“ behandelt [forall x: Calgary, Kapitel 26](https://forallx.openlogicproject.org/html/Ch26.html).

### Leere Bereiche und eigenschaftsunabhängige Aussagen

Die Beschränkung der Definition bei [12997](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:12997) auf nichtleere Mengen ist eine mögliche Einschränkung, aber für die Definition nicht nötig. Die Ersatzformeln liefern auch:

\[
\forall x\in\varnothing\,A(x)\text{ ist wahr},\qquad
\exists x\in\varnothing\,A(x)\text{ ist falsch},\qquad
\exists!x\in\varnothing\,A(x)\text{ ist falsch}.
\]

Es gibt im ersten Fall kein Element, an dem die Forderung scheitert. Damit wird kein Element der leeren Menge behauptet.

Kommt `x` in `A` gar nicht frei vor, gilt `∃x∈M A ↔ (M≠∅ ∧ A)` und `∀x∈M A ↔ (M=∅ ∨ A)`. Bei nichtleerem `M` sind beide zu `A` äquivalent. Das ist formal sinnvoll und erklärt das Sonnenbeispiel im Logikteil; ein geringer Erkenntnisgewinn ist kein Bindungsfehler.

## 4. Die Quantorensätze: richtige Behauptungen, verschiedene Beweisstände

### Aus „für alle“ folgt „es gibt“ bei nichtleerer Menge

**Fundstellen:** [Satz 13467–13479](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13467); [sprachlicher Beweis 13512–13551](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13512); [formaler Versuch 13556–13775](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13556).

Die Behauptung ist richtig, wenn die Klammern und die Abhängigkeit sichtbar sind:

\[
\bigl(M\ne\varnothing\land\forall x\in M\,A(x)\bigr)
\Rightarrow\exists x\in M\,A(x).
\]

**Kurzer Beweis:** Wähle wegen `M≠∅` ein `a∈M`. Aus der allgemeinen Voraussetzung folgt `A(a)`. Damit ist `a` ein Zeuge für die Existenzaussage. Genau diese Idee enthält der sprachliche Beweis bereits; bei der Umbenennung ist `A(a)` mitzuschreiben. Es werden Allquantor-Elimination und Existenzquantor-Einführung benutzt. Das sind die zusätzlichen logischen Regeln.

Ohne Nichtleerheit ist die Behauptung falsch: Für `M=∅` ist der Vordersatz `∀x∈M A(x)` wahr und die Existenzaussage falsch. Im formalen Versuch tritt ab [13573](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13573) dagegen neben der allgemeinen Aussage ein freies `x∈M` auf, und anschliessend wird der Allquantor mittels der falschen Definition entfernt. Die richtig gemeinte Instanziierung lautet:

\[
\bigl(a\in M\land\forall x\in M\,A(x)\bigr)
\Rightarrow\bigl(a\in M\land A(a)\bigr)
\Rightarrow\exists x\in M\,A(x).
\]

Dies ist ein Ersatz für den misslungenen formalen Beweis; es ist keine Herleitung der Quantoren allein aus Konjunktion und Implikation.

### Negation von Quantoren

**Fundstellen:** [Sätze 13932 und 13966](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:13932); formale Beweise ab [14000](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:14000) und [14431](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:14431); sprachliche Beweise ab [14291](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:14291) und [14628](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:14628).

In der hier verwendeten klassischen Logik gelten:

\[
\neg\exists x\in M\,A(x)\ \leftrightarrow\ \forall x\in M\,\neg A(x),
\qquad
\neg\forall x\in M\,A(x)\ \leftrightarrow\ \exists x\in M\,\neg A(x).
\]

Beide gelten auch für `M=∅`. In der ersten Äquivalenz sind dann beide Seiten wahr, in der zweiten beide falsch. Die Nichtleerheitsvoraussetzung kann hier entfallen.

**Begründung der ersten Äquivalenz:** Wenn kein Element `A` erfüllt, erfüllt jedes Element `¬A`. Umgekehrt würde ein Zeuge für `A` der allgemeinen Aussage `¬A` widersprechen. **Zur zweiten:** Ein Gegenbeispiel zu `A` widerlegt die allgemeine Aussage. Wenn umgekehrt kein Gegenbeispiel existierte, würde jedes Element klassisch `A` erfüllen; das widerspräche `¬∀x∈M A(x)`. Hier wird das klassische Verständnis von Negation verwendet, nicht ein Schluss von Nichtwissen auf Falschheit.

Die sprachlichen Beweise treffen damit die richtige Idee. Die formalen Beweise tragen in ihrer jetzigen Form nicht: Bereits ihre Ausgangsgleichungen `14000` und `14431` lassen die Bindung verschwinden. Beispielsweise ist [14548](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:14548), `¬∀x∈M A ↔ (x∈M ∧ ¬A)`, für `M={1,2}`, `A(x): x=1`, freie Belegung rechts `x=1`, falsch: links wahr, rechts falsch.

**Spätere tatsächliche Verwendung:** Die [Übersicht im Logikteil 31966–31971](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:31966) führt die richtigen Quantoren-Dualitäten auf. In [Restposten 29884–29923](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:29884) wird eine Negation über den äusseren Allquantor einer Folgenbedingung gezogen. **Dieser einzelne Umformungsschritt ist richtig**, sofern die innere Bedingung als feste Formel mit Parameter `ε` verstanden wird. Damit ist weder die dortige Konvergenzdefinition noch der folgende Divergenzbeweis insgesamt geprüft oder bestätigt.

## 5. Teilmenge, Gleichheit und Mengenoperationen

### Teilmenge und Mengengleichheit benötigen „für jedes“

**Fundstellen:** [Teilmenge 498–617](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:498); [Mengengleichheit 622–717](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:622); die ältere sprachliche Definition [im Logikteil 4579](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:4579).

Die Formeln `m∈M₁ ⇒ m∈M₂` bei 533 und `m∈M₁ ↔ m∈M₂` bei 652 sind richtige **Elementbedingungen**. Sie definieren aber nur dann Teilmenge bzw. Gleichheit, wenn ihre Allgemeinheit ausdrücklich mitgemeint ist. Die frühere sprachliche Gleichheitsdefinition sagt bereits richtig „jedes Element … und umgekehrt“.

Ein einzelnes Element genügt nicht: Für `M₁={1}`, `M₂={1,2}`, `m=1` ist die Mitgliedschaftsäquivalenz wahr, obwohl die Mengen ungleich sind. Ebenso ist für `M₁={1,2}`, `M₂={1}`, `m=1` die Implikation wahr, obwohl `M₁` keine Teilmenge von `M₂` ist.

Die kleinste Klarstellung ist eine allgemeine Leseregel: „In den folgenden Mengencharakterisierungen ist `m` ein beliebiges Element des festgehaltenen Bereichs; die Elementbedingung muss für jedes solche `m` gelten.“ Ausgeschrieben:

\[
\begin{aligned}
M_1\subset M_2&\ \leftrightarrow_{\rm def}\
  \forall m\,(m\in M_1\Rightarrow m\in M_2),\\
M_1=M_2&\ \leftrightarrow\
  \forall m\,(m\in M_1\leftrightarrow m\in M_2),\\
M_1=M_2&\ \leftrightarrow\ (M_1\subset M_2\land M_2\subset M_1),\\
M_1\subsetneq M_2&\ \leftrightarrow_{\rm def}\
  (M_1\subset M_2\land M_1\ne M_2).
\end{aligned}
\]

`⊂` bedeutet hier weiterhin die eigene, nicht notwendig echte Inklusion; häufig wird dafür `⊆` geschrieben. Das ist eine Notationsentscheidung. **Ein wirklicher Richtungsfehler** steht dagegen bei [599–614](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:599): `M₂⊂M₁` wird mit „M₂ ist die Obermenge von M₁“ übersetzt. Dafür muss `M₂⊃M₁` stehen, oder der Satz muss „Teilmenge“ lauten. `M₂={1}`, `M₁={1,2}` zeigt den Unterschied.

Bei Mengenungleichheit ist `M₁≠M₂ ↔ ¬(M₁=M₂)` richtig. Klassisch ergibt sich daraus ein **Existenzzeuge**:

\[
M_1\ne M_2\ \leftrightarrow\
\exists m\,\bigl((m\in M_1\land m\notin M_2)
 \lor(m\in M_2\land m\notin M_1)\bigr).
\]

Mengengleichheit als „dieselben Elemente“ kann innerhalb des eigenen Mengenbegriffs eine Definition sein. Wenn die Mengen bereits als Objekte einer Theorie vorausgesetzt werden, ist die Identifikation durch gleiche Elemente deren Extensionalitätsprinzip. In beiden Lesarten ist dies eine zusätzliche Grundlage für Mengen, keine Wahrheitstafelfolge allein. Die Standarddarstellung samt Quantoren bietet [Logic and Proof, Abschnitt 11.1](https://leanprover-community.github.io/logic_and_proof/sets.html#elementary-set-theory).

### Die Mengendifferenz ist tatsächlich falsch definiert

**Fundstellen:** [Ankündigung 919, Definition 932, zweite Charakterisierung 945](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:919).

Angekündigt wird `M₁\M₂`, dann steht

\[
M_2\setminus M_1\equiv\{m\mid m\in M_1\lor m\notin M_2\},
\]

während die nachfolgende Charakterisierung `x∈M₂\M₁ ↔ (x∈M₂ ∧ x∉M₁)` richtig ist. Für `M₁={1}`, `M₂={1,2}` nimmt die erste Formel `1` auf, die zweite schliesst es aus. In einem grösseren Bereich würde die erste auch Elemente ausserhalb beider Mengen aufnehmen.

Einheitlich könnte der ganze Block bei der zweiten Reihenfolge bleiben:

\[
M_2\setminus M_1\equiv\{m\in M_2\mid m\notin M_1\},
\qquad
\forall x\;\bigl(x\in M_2\setminus M_1
 \leftrightarrow(x\in M_2\land x\notin M_1)\bigr).
\]

Dann ist auch die Ankündigung auf `M₂\M₁` anzupassen. Wenn `M₁⊂M₂`, ist dies das Komplement von `M₁` **bezüglich `M₂`**, wie es der Text sprachlich beabsichtigt. Ein absolutes Komplement ohne Bezugsbereich wird dadurch nicht eingeführt.

Die Definitionen von Schnitt und Vereinigung bei [808–867](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:808) verwenden dagegen die passenden Verknüpfungen. Ihre Mitgliedschaftsformeln sind als allgemein geltende Charakterisierungen zu lesen. In der Einleitung [253](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:253) bleibt der Abschreibfehler aus B8: Richtig ist `A∧(B∨C) ↔ ((A∧B)∨(A∧C))`. Für `A` falsch, `B` falsch, `C` wahr ist die gedruckte rechte Seite wahr und die linke falsch. Die Übertragung bei 278–288 benutzt bereits die richtige Struktur.

### Einzelmengen, Potenzmenge und Existenz

`x∈{A} ↔ x=A` und `x∈M∪{A} ↔ (x∈M ∨ x=A)` bei [425–433](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:425) passen zusammen. Die Potenzmenge [959–965](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:959) enthält genau die Teilmengen, einschliesslich `∅` und `M` selbst, weil `⊂` hier nicht echt bedeutet. Insbesondere gilt `𝒫(∅)={∅}`.

Festzuhalten ist, ob Elemente Zeichen als Objekte oder die von Zeichen bezeichneten Objekte sind. Zwei verschiedene Namen desselben Objekts erzeugen in der zweiten Lesart keine zwei verschiedenen Mengenelemente. Das ist die Mengenfassung der Unterscheidung zwischen Zeichen und Inhalt aus Arbeitspaket 3.

Aus der Möglichkeit, eine Eigenschaft hinzuschreiben, folgt ausserdem noch nicht die Existenz einer Menge aller passenden Objekte. Für die elementaren Rechnungen genügt eine benannte Grundlage: Einzelmengen und Paare, Vereinigung, Aussonderung innerhalb gegebener Mengen und Potenzmengen stehen zur Verfügung. Das Wort „wohldefiniert“ ersetzt diese Grundlage nicht. Eine vollständige Axiomatisierung ist dafür in diesem Skript nicht zwingend; der Umfang des Vorausgesetzten muss aber sichtbar bleiben.

## 6. Symmetrische Differenz: Der Satz ist richtig, der Beweis hat Folgefehler

**Fundstellen:** [Definition 3521, Satz 3578–3586](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:3521); [zusätzliche Verneinungen 3720–3867](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:3720); [falsche Differenzrichtung 3918](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:3918); [Schluss und eigene Zweifel 4299–4380](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:4299).

Mit der richtigen Differenz gilt für alle Mengen:

\[
A\Delta B=(A\setminus B)\cup(B\setminus A),\qquad
A=B\ \leftrightarrow\ A\Delta B=\varnothing.
\]

Im Beweis wird `¬(m∈B)` mehrfach zu `¬m∉B` statt zu `m∉B` umgeschrieben. Die zusätzliche Negation kehrt die Bedingung um. Mit `A=B={1}`, `m=1` ist `m∈A ∧ ¬(m∈B)` falsch, `m∈A ∧ ¬(m∉B)` dagegen wahr. Später steht in der zweiten negierten Differenzformel nochmals `A\B`, wo `B\A` stehen muss; bei `A={1}`, `B={2}`, `m=2` haben diese Mitgliedschaftsnegationen verschiedene Werte.

Eine zweite, wichtigere Lücke liegt im Übergang von `¬(m∈AΔB)` zu „es existiert kein Element“. Für ein einzelnes freies `m` folgt das nicht: `m=1` gehört nicht zu `{2}`, aber `{2}` ist nicht leer. Die im Text ausdrücklich bemerkte Unsicherheit lässt sich durch die fehlende Allgemeinheit auflösen.

**Kurzer Ersatzbeweis in beiden Richtungen:** Für ein beliebiges `m` gilt nach den Definitionen und einer aussagenlogischen Nachrechnung

\[
m\notin A\Delta B\ \leftrightarrow\
\neg\bigl((m\in A\land m\notin B)
 \lor(m\in B\land m\notin A)\bigr)
\ \leftrightarrow\ (m\in A\leftrightarrow m\in B).
\]

Quantifiziert man **beide Elementbedingungen über alle `m`**, erhält man links „`AΔB` hat kein Element“ und rechts die Mengengleichheit. Somit folgt die behauptete Äquivalenz, auch wenn `A` oder `B` leer ist. Ihre Negation liefert `A≠B ↔ AΔB≠∅`. Die Beschränkung des ausgeschriebenen Beweisbeginns auf `A≠∅` ist damit überflüssig; im vorhandenen Beweis wird der leere Fall nicht eigens abgeschlossen.

## 7. Die leere Menge und ihre Hilfsmenge

**Fundstellen:** [Definition 1000](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:1000); [angekündigte Unabhängigkeit und Beweis 4457–4600](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:4457); [Eigenschaften 4625–4650](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:4625).

Die Konstruktion `E_M={x∈M | x∉M}` ist brauchbar: Für jedes `x` gilt `x∈E_M ↔ (x∈M ∧ ¬(x∈M))`, also hat `E_M` kein Element. Die widersprüchliche **Elementbedingung** erzeugt eine leere Aussonderung; sie wird nicht als wahre Voraussetzung angenommen. Das entspricht der Klärung des Mantras aus Arbeitspaket 3. `M` muss dazu nicht nichtleer sein; das ist eine unnötige Einschränkung, kein Fehler der Konstruktion. In der Formel bei 1000 sollten allerdings die Mengendefinition `∅≡{x∈M | x∉M}` und ihre allgemeine Mitgliedschaftscharakterisierung als zwei getrennte Ausdrücke stehen. Das dortige `↔` verbindet sonst eine Mengendefinition ohne klare Klammerung mit einer Aussage.

Der angekündigte Unabhängigkeitsbeweis zeigt bei 4600 jedoch nur `x∈Ø ↔ x∈Ø`. Das ist Reflexivität. Es vergleicht nicht zwei Hilfsmengen und begründet deshalb die behauptete Unabhängigkeit nicht.

**Ergänzung:** Für beliebige vorhandene Mengen `M,N` sind die Bedingungen `x∈M ∧ ¬(x∈M)` und `x∈N ∧ ¬(x∈N)` beide stets falsch. Daher gilt für jedes `x` die Äquivalenz `x∈E_M ↔ x∈E_N`, also `E_M=E_N` durch Mengengleichheit. Dieses gemeinsame Objekt kann `∅` genannt werden. Damit ist die Unabhängigkeit von der Hilfsmenge gezeigt, nicht eine umfassende Widerspruchsfreiheit der ganzen Mengenlehre.

Die aufgeführten Gesetze `∅⊂M`, `∅∩M=∅`, `∅∪M=M`, `M\∅=M`, `∅\M=∅` sind mit der korrigierten Differenz und der allgemeinen Lesart richtig. Die späteren Differenzbeweise benutzen bei [6884](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:6884), [7124](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:7124) und [7412](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:7412) die richtige Konjunktion mit Nichtmitgliedschaft, nicht die falsche Disjunktion aus 932. Das ist ein Grund, den ursprünglichen Definitionsfehler nicht pauschal auf alle Ergebnisse zu übertragen.

## 8. Weitere unmittelbar betroffene Beweise

### Gleichheit als Äquivalenzrelation

Die Behauptungen im Abschnitt [1078–3471](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:1078), Gleichheit sei reflexiv, symmetrisch und transitiv, sind richtig. Sie lassen sich für ein beliebiges `x` auf die entsprechenden Eigenschaften von `↔` zurückführen und anschliessend durch Extensionalität auf Mengen übertragen. Der Beweis von [2539 bis 2613](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:2539) muss dabei nicht nur ein aus `A` gewähltes Element, sondern ein beliebiges Element des Bereichs behandeln. Sonst wäre nur eine Inklusion geprüft.

Eine getrennte Behandlung leerer Mengen ist dafür nicht nötig, kann zur Anschauung aber bleiben. Stets falsche Mitgliedschaftsbedingungen haben denselben Wahrheitswert; ihre Äquivalenz ist wahr. Weder „identitiv“ für reflexiv noch „kommutativ“ für symmetrisch ist hier ein mathematisches Gegenbeispiel, sondern eine eigene Benennung.

### Paarmengen und Reihenfolge

Der Satz `{A,B}={B,A}` ist richtig, aber [im Beweis 7724 und 7783](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:7724) wird die Paarmenge durch `x∈A ∨ x∈B` beschrieben. Richtig ist `x=A ∨ x=B`. Die gedruckte Bedingung beschreibt bei Mengen `A,B` deren Vereinigung, nicht die Menge mit den beiden Elementen `A,B`. Für `A=B=∅` ist `∅∈{A,B}` wahr, `∅∈A ∨ ∅∈B` aber falsch.

Der örtliche Ersatz lautet für beliebiges `x`: `x∈{A,B} ↔ (x=A∨x=B) ↔ (x=B∨x=A) ↔ x∈{B,A}`. Die unmittelbar vorher eingeführte Einzelmengendefinition liefert genau diese Bedingung. Der folgende Beweis [ab 7916](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:7916) benutzt bereits Gleichheit mit den Elementen. Bei [8431](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:8431) steht allerdings eine tautologische Mitgliedschaftsäquivalenz mit derselben Reihenfolge auf beiden Seiten, wo rechts `{A,B}` stehen muss.

### Schnitt und Vereinigung bei Teilmengen

**Fundstellen:** [Satz 10300–10326](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:10300); [Beweisformeln 10408–10482](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:10408); [zitiertes logisches Grundgerüst 288252–288253](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:288252).

Unter `M₁⊂M₂` gelten `M₁∩M₂=M₁` und `M₁∪M₂=M₂`. Im Satz steht für die Vereinigung bloss `M₂=M₂∪M₂`. Das ist eine wahre Idempotenzformel, verfehlt aber die anschliessend bewiesene Behauptung. Im Beweis steht bei 10409 und 10461 hingegen die **falsche** Äquivalenz `(m∈M₁∨m∈M₂) ↔ m∈M₁`.

Gegenbeispiel mit nichtleeren Mengen: `M₁={1}`, `M₂={1,2}`, `m=2`. Die Inklusion gilt, die Vereinigung enthält `2`, die kleinere Menge nicht. Rechts muss jeweils `m∈M₂` stehen. Für Aussagen `P⇒Q` gilt `P∧Q ↔ P` und `P∨Q ↔ Q`. Das zitierte Grundgerüst enthält bei 288253 `(P⇒Q) ↔ ((P∨Q)⇒Q)`, was ebenfalls richtig ist; die falsche Folgerung entsteht an der Anwendung im Mengenteil. Nach der Korrektur funktioniert der Beweis auch für leere Mengen.

### Paarweise disjunkt und paarweise verschieden

Die Definition bei [10537–10565](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:10537) ist in ihrer Formel brauchbar: Für alle `A,B∈𝓜` soll `A≠B ⇒ A∩B=∅` gelten. Das ist nicht dasselbe wie die dort hinzugefügte Bezeichnung „paarweise verschieden“: `{1}` und `{1,2}` sind verschieden, aber nicht disjunkt.

Die Umformulierung `A∩B≠∅ ⇒ A=B` ist die richtige Kontraposition. Im Beweis wird jedoch [bei 10703 und 10730](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:10703) aus einer Implikation eine Äquivalenz gemacht. **Dieser Übergang ist nicht durch blosse Aussagenlogik gerechtfertigt.** Unter der eigenen Definition eines Mengensystems [im Logikteil 2309](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:2309) sind sämtliche Klassen nichtleer. Dann ist die stärkere Äquivalenz tatsächlich herleitbar: Aus `A∩B=∅` folgt `A≠B`, weil bei `A=B` der Schnitt die nichtleere Menge `A` wäre. Diese zusätzliche Begründung fehlt. Lässt man auch leere Klassen zu, widerlegt `A=B=∅` die Äquivalenz: links falsch, rechts wahr. Die kleinste und allgemein gültige Reparatur ist, durchgehend bei der vorausgesetzten Implikation und ihrer Kontraposition zu bleiben. Das `0` bei 10730 wäre zudem durch das Mengensymbol `∅` zu ersetzen.

### Ersetzung gleicher Mengen

Der Satz [11105–11110](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:11105) ist richtig: Aus `A=C` folgen die sechs Gleichungen mit Schnitt, Vereinigung und Differenz, jeweils in beiden Argumentstellen. Für beliebiges `x` setzt man die Äquivalenz `x∈A ↔ x∈C` in die Mitgliedschaftsbedingungen ein und schliesst anschliessend auf Mengengleichheit. Bei der zweiten Stelle der Differenz wird auch die Negation ersetzt. Das ist eine unmittelbare Anwendung der in Arbeitspaket 3 geklärten Ersetzungsregel.

Die ausgeschriebenen Beweise haben weitere örtliche Fehler. Ein zentraler davon ist [12295 und 12312](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:12295): Unter `A=C` steht dort `(x∈A ∧ x∈B) ↔ (x∈C ∧ ¬(x∈B))`. Für `A=C=B={1}`, `x=1` ist links wahr und rechts falsch. Links fehlt die Negation von `x∈B`; die richtige Struktur war bei 12229 bereits vorhanden. Ausserdem stehen bei [11251](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:11251) und [11366](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:11366) blosse Mengensymbole statt der Mitgliedschaftsaussage `x∈B`, bei [11471](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:11471) `A∩A` statt `B∩A` und bei [12017](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:12017) eine Mengenvereinigung statt der Disjunktion der Mitgliedschaftsaussagen. Mengen und Wahrheitswerte dürfen nicht als dieselbe Art von Ausdruck eingesetzt werden. Die sechs Sätze lassen sich mit dem gemeinsamen Elementbeweis erhalten; nicht jede Zwischenzeile ist damit bestätigt.

## 9. Folgen für Relationen, Funktionen und Partitionen

### Eindeutigkeit von Relationen

**Fundstellen:** [Linkseindeutigkeit 17422, Rechtseindeutigkeit 17474](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:17422); [Funktion 18962–19010](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:18962).

Für `R⊂X×Y` sind passende Formeln:

\[
\begin{aligned}
\text{linkseindeutig: }&\quad
\forall x,x'\in X\;\forall y\in Y\;
 (((x,y)\in R\land(x',y)\in R)\Rightarrow x=x'),\\
\text{rechtseindeutig: }&\quad
\forall x\in X\;\forall y,y'\in Y\;
 (((x,y)\in R\land(x,y')\in R)\Rightarrow y=y'),\\
\text{linkstotal: }&\quad \forall x\in X\;\exists y\in Y\;(x,y)\in R.
\end{aligned}
\]

Bei der gedruckten Linkseindeutigkeit laufen `m₂` über die erste und `m₃` über die zweite Menge, obwohl die Paare die umgekehrte Zuordnung benötigen. Für `X={1,2}`, `Y={3}`, `R={(1,3),(2,3)}` wird die gedruckte Formel dadurch leererweise wahr: Ihr erstes Paar hat eine zweite Koordinate aus `X` und liegt nie in `R`. Die Relation ist tatsächlich nicht linkseindeutig. Auch der sprachliche Text hat ein falsches Paar `(m₃,m₃)` statt `(m₃,m₂)`.

Bei der Rechtseindeutigkeit stehen im Vordersatz einmal `R_l` und einmal `R_r`, statt zweimal derselben Relation. Setzt man `X={1,4}`, `Y={2,3}`, `R_l={(4,2)}` und `R_r={(1,2),(1,3)}`, ist die gemischte Bedingung wahr: Kein Eingang tritt in beiden Relationen auf. Aber `R_r` ist nicht rechtseindeutig. Das Gegenbeispiel verwendet nur nichtleere Mengen und Relationen und liegt damit auch innerhalb der eigenen Einschränkung. Das ist kein neuer Relationsbegriff, sondern ein Variablenfehler.

Die Funktionsdefinition „linkstotal und rechtseindeutig“ ist nach diesen Korrekturen richtig und gleichbedeutend mit `∀x∈X ∃!y∈Y ((x,y)∈f)`. Hier wird die Eindeutigkeitsprüfung tatsächlich weiterverwendet. Der Ausschluss leerer Relationen und leerer Definitionsbereiche bei [16244–16287](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:16244) ist eine eigene Einschränkung. Er sollte als solche stehen; die leere Relation ist in der üblichen Definition zulässig. Für die im Manuskript zugelassenen nichtleeren Bereiche lässt sich weiterarbeiten.

### Partitionen: Mitgliedschaft in der Potenzmenge ist nicht Teilmengenbeziehung

**Fundstellen:** [Definition 17892–17981](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:17892); [Äquivalenzrelation erzeugt Partition 18028–18348](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:18028); [Rückrichtung ab 18370](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:18370).

Die Formel `𝔓∈𝒫(M)` behauptet `𝔓⊂M`. Der sprachliche Text will dagegen ein System von Teilmengen, also `𝔓⊂𝒫(M)`; gleichbedeutend wäre `𝔓∈𝒫(𝒫(M))`. Bei `M={1,2}` ist `𝔓={{1},{2}}` eine Partition, aber kein Element von `𝒫(M)`, weil seine Elemente Teilmengen und keine Zahlen aus `M` sind.

Auch `M_T∈𝔓 ↔ ∃x,y∈M ((x,y)∈M_T)` charakterisiert keine Äquivalenzklasse: Ein Block soll Elemente von `M` enthalten, nicht geordnete Paare. Die Existenz irgendeines Paares sichert weder vollständige Klassen noch Überdeckung noch Disjunktheit. Das anschliessende `y≅y` muss zudem, wenn die Beziehung zweier Elemente gemeint ist, `x≅y` heissen.

Eine von der Relation unabhängige Definition ist:

\[
\mathfrak P\subset\mathcal P(M),\qquad
\varnothing\notin\mathfrak P,\qquad
\bigcup_{B\in\mathfrak P}B=M,\qquad
\forall B,C\in\mathfrak P\;(B\ne C\Rightarrow B\cap C=\varnothing).
\]

Für eine vorgegebene Äquivalenzrelation `R` ergänzt man gesondert `[x]_R={y∈M | (x,y)∈R}` und `𝔓_R={[x]_R | x∈M}`. Der spätere Beweis verwendet mit `M_x` bei [18113](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:18113) bereits genau diese Klassenidee. Reflexivität gibt `x∈[x]_R`, also Nichtleerheit und Überdeckung. Treffen sich zwei Klassen in `z`, liefern Symmetrie und Transitivität für jedes Element der einen Klasse die Zugehörigkeit zur anderen und umgekehrt. Damit sind sie gleich. Diese Schritte schliessen den Grundgedanken an die korrigierten Definitionen an.

In der Rückrichtung muss jedes `x∈M` in genau einem Block liegen. Das folgt aus Überdeckung und paarweiser Disjunktheit der nichtleeren Blöcke, nicht aus der gedruckten Existenzformel allein. Die so definierte Relation „liegen im selben Block“ ist reflexiv und symmetrisch; für Transitivität müssen die beiden Blöcke mit dem gemeinsamen mittleren Element gleich sein. Die Partitionsdefinition ist somit eine echte Voraussetzung späterer Beweise und keine bloss äusserliche Schreibfrage. Die übrigen Beweiszeilen und späteren Partitionsrechnungen sind hier nicht vollständig einzeln geprüft.

## 10. Quantifikation über Aussagen und Abhängigkeiten

Bei [26583 im Logikteil](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:26583) wird ein logischer Satz mit `∀A,B∈Ω C` beschrieben. Die Unterscheidung aus Arbeitspaket 3 bleibt nötig: Objektvariablen der Mengenlehre, Formelplatzhalter und Wahrheitswerte sind nicht automatisch dieselben Objekte. Die Quantorendefinition repariert diese Ebenenfrage nicht von selbst.

Für eine aussagenlogische Formel `F(p,q)` genügt als metasprachliche Definition: „Für jede Wahrheitswertbelegung `v` gilt `v(F)=1`.“ Äquivalent kann man die beiden Eingänge über `{0,1}` laufen lassen und die zugehörige Wahrheitsfunktion auswerten. Soll stattdessen über Formelobjekte in `Ω` quantifiziert werden, braucht man eine Beziehung „diese Formel ist unter `v` wahr“. Das Formelobjekt selbst kann nicht ohne Erklärung zugleich als seine Wahrheitsbehauptung dienen. Eine Einschränkung auf gemeinsam wahre Voraussetzungen darf ausserdem nicht unbemerkt die vier Belegungen einer Wahrheitstafel beschneiden.

Die bereits geprüfte Ersetzung für wahrheitsfunktionale Formeln gilt weiterhin. Bei Formeln mit Quantoren müssen darüber hinaus Geltungsbereiche und das Vermeiden eingefangener Variablen beachtet werden; der aussagenlogische Beweis allein behandelt dies noch nicht.

| Grundlage / Korrektur | Tatsächliche nachfolgende Verwendung | Prüfstand |
| --- | --- | --- |
| Allgemeine Mitgliedschaftscharakterisierung und Extensionalität | Mengengleichheit als Äquivalenzrelation; Schnittkommutativität ab 8874; sechs Ersetzungssätze ab 11081 | Die Grundbehauptungen sind tragfähig; einzelne örtliche Fehler sind oben benannt. |
| Richtige Differenz | Symmetrische Differenz ab 3521; leere Menge und Differenzen ab 6884; Ersetzung 12159–12722 | Die spätere Verwendung folgt überwiegend der richtigen Mitgliedschaftsregel; zusätzliche Negationsfehler bleiben zu korrigieren. |
| Teilmenge und aussagenlogisches Grundgerüst | Nichtleere Obermengen ab 10176; Schnitt/Vereinigung ab 10296 | Das Obermengenargument ist richtig. Der Vereinigungsschritt im Folgesatz ist falsch abgeschrieben. |
| Einzelmenge statt Vereinigung ihrer Elemente | Paarmengen ab 7685; anschliessend geordnete Paare und Relationen | Der Reihenfolgensatz bleibt richtig; sein Elementbeweis ist zu ersetzen. Keine vollständige Prüfung der ganzen Konstruktion geordneter Paare. |
| Quantoren und Nichtleerheit | Satz 13479; Quantorennegation 13932/13966; Folgenumformung in Restposten 29923 | Behauptungen bzw. benannter Folgeschritt richtig; formale Ausgangsbeweise mit Bindungsverlust ersetzen. |
| Eindeutigkeit und richtige Variablenbereiche | Relationen 17422/17474, Funktionen 18962 | Nach Korrektur passt die Funktionsidee „zu jedem Eingang genau ein Ausgang“. |
| Teilmengen einer Potenzmenge, Klassen und Überdeckung | Partition ↔ Äquivalenzrelation ab 18028/18370 | Definition braucht die oben ausgeschriebenen Bedingungen; erst dann stehen die verwendeten Voraussetzungen zur Verfügung. |
| Mengenbildung nach einer Eigenschaft und saubere Bindung | Minimum- und Induktionsargument aus Arbeitspaket 2 | Mengen von Gegenbeispielen müssen zulässige Aussonderungen sein; Induktionsanfang und allgemeiner Induktionsschritt müssen zusammen vorausgesetzt werden. Die frühere Prüfung wird dadurch ergänzt, nicht ersetzt. |

## 11. Kleinstes zusammenhängendes Reparaturpaket und Kontrolle

1. Die Bedeutung von `A(x)`, freier und gebundener Variable, Geltungsbereich und zulässiger Umbenennung kurz vor der ersten Quantorendefinition erklären. Quantoren als eigene logische Mittel einführen.
2. **Beide** Einführungsstellen der Quantoren korrigieren; für `∃!` den Existenzzeugen und die allgemeine Eindeutigkeit gemeinsam binden. Leere Bereiche erklären und Nichtleerheit nur bei den Sätzen verlangen, die sie brauchen.
3. Bei Teilmenge, Mengengleichheit und Mitgliedschaftscharakterisierungen eine ausdrückliche allgemeine Lesekonvention oder die ausgeschriebenen Quantoren ergänzen. Den Richtungsfehler beim Obermengensymbol berichtigen.
4. Die Differenzdefinition samt Ankündigung vereinheitlichen; Schnitt, Vereinigung, Einzelmenge, Potenzmenge und Aussonderung mit ihrer Existenzgrundlage verbinden. Symbolgleichheit und Gleichheit der bezeichneten Objekte auseinanderhalten.
5. Den Unabhängigkeitsbeweis der leeren Menge mit zwei Hilfsmengen führen. Den Beweis über die symmetrische Differenz durch den allgemeinen Elementbeweis schliessen; zusätzliche Negationen und vertauschte Differenzrichtungen berichtigen.
6. Bei Paarmengen Gleichheit mit den Elementen statt Mitgliedschaft in den Elementen einsetzen. Die falschen Vereinigungsschritte und Differenz-Zwischenzeilen reparieren. Bei paarweiser Disjunktheit mit Implikation und Kontraposition arbeiten.
7. Bei Links-/Rechtseindeutigkeit die Bereiche und Relationsnamen korrigieren. Partition als System nichtleerer, disjunkter, überdeckender Teilmengen definieren und die durch eine Äquivalenzrelation erzeugten Klassen gesondert angeben.
8. Die Quantorensätze mit den kurzen Beweisen aus Abschnitt 4 begründen. Bei Quantifikation über Aussagen die metasprachliche Wahrheit unter allen Belegungen kenntlich machen.

Die wesentlichen Ersatzbehauptungen wurden oben allgemein begründet; die falschen Formeln haben konkrete Gegenbeispiele. Zusätzlich wurden mit Python sämtliche 64 Kombinationen aus einer Teilmenge `M` von `{1,2,3}` und einer dort festgelegten Eigenschaft geprüft: beide Quantorendualitäten, Eindeutigkeit und der Schluss von Allgemeinheit auf Existenz unter Nichtleerheit. Für alle 64 Mengenpaare wurden Inklusion, Gleichheit, Differenz, symmetrische Differenz, die Gesetze mit der leeren Menge und die Teilmengengesetze kontrolliert; für alle 512 Mengentripel Distributivität und die sechs Ersetzungen unter `A=C`. Die zentralen Gegenbeispiele zu Bindungsverlust, Eindeutigkeit, Differenz, Vereinigung, Differenzersetzung und Linkseindeutigkeit wurden ebenfalls rechnerisch bestätigt. Endliche Kontrollen ergänzen die allgemeinen Begründungen, ersetzen sie aber nicht; eine vollständige Lean-Formalisierung wurde nicht durchgeführt.

**Arbeitspaket 4 ist damit als dokumentierte fachliche Prüfung abgeschlossen.** Die Übernahme der Vorschläge ins Manuskript bleibt ein eigener Schritt. Als nächste nummerierte Aufgabe folgt Arbeitspaket 5 zum Rechnen und zu den Zahlbereichen.
