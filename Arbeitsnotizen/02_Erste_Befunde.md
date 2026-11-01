# Erste sachliche Befunde

Stand: 1. November 2026. Gezielte erste Prüfung, keine vollständige Fehlerliste. Das Manuskript wurde nicht verändert. Die Reihenfolge folgt ungefähr der Bedeutung für das Fundament, nicht der Reihenfolge im Buch.

„Falsch“ bezeichnet unten eine nachprüfbar falsche Aussage oder Formel. „Begründung offen“ bedeutet ausdrücklich nicht, dass die behauptete mathematische Eigenschaft falsch wäre. Vorschläge sind Prüf- oder Reparaturmöglichkeiten, noch keine vereinbarten Änderungen.

## B1 – Die Definition von „Aussage“ reicht für die spätere Wahrheitslogik nicht aus

**Fundstelle:** [Logik, Zeilen 554–645](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:554).

**Text:** „Aussagen sind Anneinanderreihungen von Symbolen“. Danach: „Jeder umgangssprachliche Satz ist also eine Aussage.“ Auch „dies ist“ wird unter dieser Definition als Aussage zugelassen.

**Befund:** Als eigener, weiter Name für Symbolketten ist das eine mögliche Festlegung. Daraus folgt aber nicht, dass jede so bezeichnete Kette wahr oder falsch sein kann. „Bitte komm!“ und „Welche Uhrzeit?“ sind Symbolketten und sprachliche Sätze; sie haben nicht ohne zusätzliche Interpretation die Wahrheitswerte, mit denen die anschliessende Aussagenlogik rechnet. Auch die Zeichenzahl entscheidet nicht darüber: Ein einzelnes vereinbartes Zeichen kann eine vollständige Aussage vertreten.

**Kleine Reparaturmöglichkeit:** Den weiten Begriff beibehalten, aber ausdrücklich die für die nachfolgenden Wahrheitsverknüpfungen geeigneten Aussagen abgrenzen. Offenlegen, ob „Aussage“ jeweils die Zeichenkette oder ihren unter einer Interpretation bestimmten Inhalt meint. Die Unterscheidung von sprachlichem Satz, Aussage und Inhalt wird beispielsweise in den [Logic Notes der ANU](https://users.cecs.anu.edu.au/~jks/LogicNotes/glossary/g_sentence.html) erläutert.

## B2 – Das Lage-Beispiel ist kein Gegenbeispiel zur Kommutativität der Konjunktion

**Fundstellen:** [Kommutativitätssatz](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:79752) und [Beispiel „topologische Widersprüchlichkeit“](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:80851), insbesondere die Folgerung bei Zeile 81022.

**Befund:** Die Beobachtung über Sprache ist richtig: Ein Satzteil wie „vorher wurde … geschrieben“ kann nach dem Versetzen an eine andere Textstelle etwas anderes besagen. Daraus folgt jedoch keine Widersprüchlichkeit der klassischen Aussagenlogik. Beim Vertauschen der Schriftstücke wird zugleich der Bezug des Wortes „vorher“ verändert. Es werden damit nicht mehr dieselben fest interpretierten Aussagen verglichen.

Bei festgehaltener Interpretation gilt stets:

\[
(A\land B)\leftrightarrow(B\land A).
\]

Zur Diagnose kann man vorübergehend den Schreibkontext mit einem Index festhalten. Im Beispiel werden dann Ausdrücke in verschiedenen Kontexten verglichen, etwa \(A_{c_1}\land B_{c_1}\) und \(B_{c_2}\land A_{c_2}\). Dass diese verschiedene Wahrheitswerte haben können, ist mit der obigen Regel vereinbar. Das ist eine Erläuterung, kein Vorschlag, das Skript überall mit solchen Indizes zu belasten. Für die Standardsemantik siehe [Poole/Mackworth, Semantics of the Propositional Calculus](https://www.cs.ubc.ca/~poole/aibook/2e/html2e/ArtInt2e.Ch5.S1.SS2.html); zur festen Interpretation kontextabhängiger Ausdrücke die [ANU-Notizen](https://users.cecs.anu.edu.au/~jks/LogicNotes/glossary/g_sentence.html).

**Wesentliche Korrektur:** Die Schlussfolgerung, das Beispiel zeige eine innere Widersprüchlichkeit der elementaren Logik, ist nicht gerechtfertigt. Es zeigt eine Voraussetzung ihrer Anwendung auf natürliche Sprache: Der Bezug der Zeichen muss festgehalten werden.

Auch das wiederholte Mantra benötigt deshalb eine genauere Erklärung. Widerspruchsfreiheit allein ist nicht dasselbe wie ein unveränderter Bezug. Eine Aussage kann in einer Situation wahr und in einer anderen falsch sein, ohne dass die Logik widersprüchlich wäre. Ebenso ist eine stets falsche Formel wie \(P\land\neg P\) ein zulässiger Gegenstand der klassischen Logik; gefährlich wird eine solche Formel als akzeptierte Voraussetzung einer Theorie.

**Zusätzlicher Abgleich:** Deine neue Rechts-links-Fassung enthält gegenseitige Verweise. Deine [Metasymboldefinition bei Zeile 1395](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:1395) schliesst direkten oder indirekten Selbstverweis bereits aus. Wenn die Verweise der neuen Fassung in diesem Sinn gemeint sind, liegt das Beispiel ausserhalb dieser eigenen Zulässigkeitsbedingung. Selbstbezug ist zudem nicht generell mit logischem Widerspruch gleichzusetzen.

**Was erhalten werden kann:** Das Beispiel selbst und der wiederholte Hinweis auf Voraussetzungen. Zu ändern wäre zunächst die daraus gezogene Schlussfolgerung.

## B3 – Totale Vergleichbarkeit ist nicht schon das Minimumprinzip

**Fundstellen:** [Totale Vergleichbarkeit, Zahlenteil ab Zeile 3412](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:3412), [Minimumsatz ab Zeile 9791](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:9791), [Induktionsbeweis ab Zeile 15227](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15227).

**Befund zur Kürzestzusammenfassung:** Aus der Vergleichbarkeit zweier Elemente allein folgt nicht, dass jede nichtleere Teilmenge ein kleinstes Element hat. Gegenbeispiel: Die ganzen Zahlen sind in ihrer üblichen Ordnung total vergleichbar; die Menge aller ganzen Zahlen hat dennoch kein kleinstes Element.

Im Skript überspringst du diesen Unterschied nicht einfach: Du stellst einen eigenen Minimumsatz für die Symbolketten auf. Dein Induktionsbeweis beruft sich ausdrücklich darauf. Die genauere Beschreibung deines Versuchs lautet also: Vergleichbarkeit **zusammen mit den weiteren Eigenschaften endlicher Symbolketten** soll den Minimumsatz begründen, und dieser soll die Induktion tragen.

**Begründung offen:** Die entscheidende Last liegt auf diesen weiteren Eigenschaften. Die Herleitung der Induktion aus einem passenden Minimumprinzip ist ein bekannter Weg; sie gewinnt ihre Kraft nicht aus totaler Vergleichbarkeit allein. Eine explizite Darstellung dieses Weges für die positiven ganzen Zahlen findet sich in den [Vorlesungsnotizen der Universität Southampton](https://www.southampton.ac.uk/~wright/1001/appendix-a---well-ordering-principle.html).

## B4 – „Induktion aus elementarer Logik“ und „Peanos Axiome sind keine“ sind zu starke Schlussfolgerungen

**Fundstellen:** [Eigene Zahlendefinition, besonders Zeilen 10479–10526](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10479), [Peano-Kapitel](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:14302), [Induktionssatz](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15227), [Nachbemerkung](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15462).

**Befund:** Der Beweis benutzt eine besondere Struktur: endliche Ketten eines Grundsymbols, Nachfolger und Vorgänger, eine Ordnung und einen Minimumsatz. Das ist mehr als elementare Logik. Logik allein legt nicht fest, welche Zahlenstruktur vorliegt.

In der eigenen Zahlendefinition wird Endlichkeit zusätzlich durch das Verbot einer unendlichen streng absteigenden Zahlenfolge beschrieben. In dieser Beschreibung werden \(\mathbb N\), Zahlenfolgen und die Ordnung der Zahlen schon benutzt, während die Zahlen gerade definiert werden sollen. Das ist eine **zu klärende Abhängigkeit**. Als Erläuterung zu einem vorab verstandenen Endlichkeitsbegriff kann der Satz dienen; als eigenständige erste Definition benötigt er eine Grundlage, die im Text noch nicht klar benannt wird.

Auch „Weitere Elemente … seien nicht vorhanden“ ist wesentlich. Es soll offenbar ausschliessen, dass die Konstruktion zusätzliche Elemente enthält, die durch endlich oft wiederholte Nachfolgerbildung nicht erreicht werden. Diese Festlegung darf beim Prüfen des Induktionsanspruchs nicht übergangen werden.

**Kein Befund, dass die Grundidee unbrauchbar wäre:** Eine Konstruktion, in der Peano-Eigenschaften bewiesen werden, ist möglich und sinnvoll. Dass diese Eigenschaften innerhalb einer anderen Grundlage Sätze werden, nimmt ihnen nicht ihren Status als Axiome einer Peano-Axiomatisierung. Axiom und Satz sind relativ zu der jeweils gewählten Grundlage. Die Behauptung, Induktion werde in der üblichen mathematischen Literatur überhaupt nicht bewiesen, ist deshalb ebenfalls zu pauschal; die verlinkten Southampton-Notizen beweisen sie beispielsweise aus dem dortigen Minimumprinzip.

**Nächste Prüfung:** Genau festlegen, was über endliche Symbolketten bereits angenommen wird. Erst dann lässt sich sagen, ob ein bestimmter Beweis zirkulär ist oder eine zulässige Herleitung innerhalb dieser Grundlage liefert. Ein pauschales Urteil über sämtliche Beweise wäre jetzt voreilig.

## B5 – Im Minimum- und Induktionsbeweis gibt es örtliche Lücken und falsche Variablen

**Minimumsatz:** [Zahlenteil, Zeilen 9857–10006](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:9857).

Du setzt \(D=\{C\in M\mid C\le B\}\) und \(E=\{C\in M\mid C\ge B\}\), wobei \(B\in M\) gewählt ist. Die Idee, das Minimum im endlichen Anfangsstück \(D\) zu suchen, ist brauchbar. Genau zu begründen ist, warum es nur endlich viele verschiedene nichtleere Ketten desselben Grundsymbols unterhalb einer gegebenen endlichen Kette gibt. Das sollte durch ihre möglichen Anfangsstücke begründet werden. Die nachfolgende Passage verwechselt jedoch \(B\), \(C\) und \(D\) und stellt das Argument so nicht nachvollziehbar dar.

Mit \(G=\min D\) und \(B=\min E\) steht danach bei Zeile 9989:

\[
\min M=\min\{G,C\}.
\]

Das \(C\) ist dort kein dafür ausgewähltes festes Element. Vermutlich ist \(B\) gemeint; nach Begründung von \(G\le B\) kann direkt \(\min M=G\) gefolgert werden. Der Satztext enthält zusätzlich die falsche Gleichsetzung „endlich viel“ bedeute insbesondere „mindestens ein“: Endliche Mengen können leer sein. Nichtleerheit muss gesondert gefordert werden.

**Induktionsbeweis:** [Zahlenteil, Zeilen 15342–15423](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15342).

Du setzt \(W=\{n\in\mathbb N\mid\neg A_{n+1}\}\) und \(w=\min W\). Hier fehlen ausdrücklich zwei Verbindungen:

1. Aus einem Gegenbeispiel \(\neg A_m\) mit \(m\ne1\) wird mithilfe des Vorgängerlemmas gefolgert, dass \(W\ne\varnothing\).
2. Für \(A_w\) ist zu unterscheiden: Ist \(w=1\), gilt die Anfangsvoraussetzung. Ist \(w>1\), hat \(w\) einen Vorgänger \(v\), und wegen der Minimalität von \(w\) liegt \(v\) nicht in \(W\). Daher gilt \(A_{v+1}=A_w\).

Der Text behauptet die zweite Verbindung nur mit „Also müsste … wahr sein“. Anschliessend wechseln die Indizes von \(w\) zu \(W\) und zu einem nicht eingeführten \(p\). Das sind konkrete reparierbare Stellen. Nach ihrer Reparatur bleibt die grundlegende Frage nach den Voraussetzungen des Minimumsatzes aus B4 bestehen.

## B6 – Die Quantorendefinitionen lassen die Bindung der Variablen verloren gehen

**Fundstelle:** [Mengenlehre, Definition `def:Quantoren`, Zeile 12986](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:12986).

Unter anderem steht dort sinngemäss:

\[
(\exists x\in M:A)\;\Longleftrightarrow_{\rm def}\;x\in M\land A,
\]

und entsprechend für den Allquantor mit \(x\in M\Rightarrow A\).

**Befund: als formale Äquivalenzen falsch.** Rechts ist \(x\) frei, links gebunden. Für \(M=\{1,2\}\) und \(A(x)\) gleich \(x=1\) ist die Existenzaussage wahr. Die rechte Seite ist bei der Belegung \(x=2\) falsch. Das sind nicht dieselben Aussagen.

Die korrekten Abkürzungen lauten, sofern unbeschränkte Quantoren bereits eingeführt sind:

\[
\exists x\in M:A(x)\quad\Longleftrightarrow\quad
\exists x\,(x\in M\land A(x)),
\]

\[
\forall x\in M:A(x)\quad\Longleftrightarrow\quad
\forall x\,(x\in M\Rightarrow A(x)).
\]

Damit werden Quantoren noch nicht aus aussagenlogischen Verknüpfungen definiert; die unbeschränkten Quantoren brauchen ihrerseits eine Bedeutung. Sind die bisherigen Zeilen nur als sprachliche Merkhilfen gemeint, muss das kenntlich gemacht werden.

Auch die dortige Formel für „genau ein“ bindet ihre Variablen nicht richtig. Eine mögliche Form ist:

\[
\exists x\in M\;\bigl(A(x)\land
\forall y\in M\,(A(y)\Rightarrow y=x)\bigr).
\]

## B7 – Die Mengendifferenz wird mit widersprechenden Formeln eingeführt

**Fundstelle:** [Mengenlehre, Zeilen 875–951](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:875).

Zuerst wird \(M_1\setminus M_2\) angekündigt. Die Formel lautet dann aber:

\[
M_2\setminus M_1\equiv\{m\mid m\in M_1\vee m\notin M_2\}.
\]

Die nachfolgende Formel bei Zeile 940 beschreibt dagegen die übliche Bedeutung von \(M_2\setminus M_1\):

\[
x\in M_2\setminus M_1\quad\Longleftrightarrow\quad
x\in M_2\land x\notin M_1.
\]

**Befund: eindeutig falsche erste Formel.** Mit \(M_1=\{1\}\) und \(M_2=\{1,2\}\) gehört \(1\) nach der ersten Formel zur Differenz, nach der zweiten gerade nicht. Das ist ein erheblicher lokaler Fehler, kein Einwand gegen deinen Aufbau der Mengenlehre. Bei der Korrektur sind sowohl die Reihenfolge der Mengen als auch \(\vee\)/\(\land\) zu beachten.

## B8 – Ein als Distributivgesetz zitiertes Gesetz ist falsch abgeschrieben

**Fundstelle:** [Mengenlehre, Einleitung ab Zeile 181](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:181).

Dort steht:

\[
A\land(B\lor C)\leftrightarrow A\land B\lor A\lor C.
\]

**Befund: falsch.** Mit \(A\) falsch, \(B\) falsch und \(C\) wahr ist die linke Seite falsch und die rechte wahr. Richtig wäre:

\[
A\land(B\lor C)\leftrightarrow
(A\land B)\lor(A\land C).
\]

Die anschliessende Übertragung auf Mengenelemente verwendet diese richtige Struktur bereits. Deshalb ist dies zunächst als Abschreibfehler an dieser Fundstelle zu behandeln, nicht als Widerlegung der entsprechenden ganzen Beweisfamilie.

## B9 – Die Einordnung rationaler und irrationaler Zahlen enthält klare Falschaussagen

**Fundstellen:** [Zahlenteil, Zeilen 15835–16008](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15835).

- **„Jede rationale Zahl ist eine irrationale Zahl.“ – Falsch.** Rationale und irrationale Zahlen schliessen sich aus. Irrationale Zahlen sind gerade die reellen Zahlen, die nicht rational sind. Zum Beispiel ist \(1=1/1\) rational und nicht irrational. Gemeinsam bilden beide die reellen Zahlen.
- **„Der Prototyp einer irrationalen Zahl ist \(\sqrt{-1}\).“ – Falsch.** Gemeint ist vermutlich „imaginären“. Irrationale Zahlen sind reell; eine komplexe Zahl \(i\) mit \(i^2=-1\) ist nicht reell.
- **Die Erklärung, rationale Zahlen seien als Ziffernfolge darstellbar, grenzt sie nicht ab.** Auch irrationale reelle Zahlen haben Dezimaldarstellungen. Der Unterschied liegt darin, dass rationale Zahlen als Quotienten ganzer Zahlen mit Nenner ungleich null darstellbar sind; ihre Dezimaldarstellung endet oder wird periodisch. Beispielsweise hat \(\sqrt2\) ebenfalls eine Dezimaldarstellung, aber keine endende oder schliesslich periodische.

Die scherzhafte Rede von „vernünftig“ und „unvernünftig“ kann bleiben. Die daraus abgeleiteten mathematischen Einordnungen müssen stimmen. Dass du \(0\) nicht zu den natürlichen Zahlen zählst, ist hingegen eine zulässige Konvention.

## B10 – Im Handschlagbeweis ist eine Gleichungszeile falsch

**Fundstellen:** [Zahlenteil, Lösung ab Zeile 19089](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19089); wiederholt [ab Zeile 22304](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22304).

Nach einer richtigen Umformung steht:

\[
\frac{n(n-1)}2=\frac{n^2-n}2+n.
\]

**Befund: falsch.** Schon bei \(n=2\) ergäbe dies \(1=3\). Links fehlt offenbar ebenfalls \(+n\). Die Handschlagformel selbst und die Grundidee des Induktionsbeweises werden dadurch nicht falsch.

## Weitere vorgemerkte Punkte

Diese Liste ist keine Bescheinigung, dass die übrigen Stellen korrekt seien. Bereits sichtbar sind unter anderem:

- Im Satz zur totalen Vergleichbarkeit bei Zeile 3412 steht, dass B und C aus Symbolen **C** bestehen; nach Definition und Beweis ist offenbar **A** gemeint. Ein solcher Buchstabenfehler wiegt hier schwer, weil er mit dem Ausschluss von Selbstverweisen kollidiert.
- Die Induktionsformel im Peano-Kapitel hat Quantoren- und Bindungsprobleme; der sprachliche Begleittext ist näher an der beabsichtigten Aussage. Der allgemeine Induktionsschritt gehört als eigene Voraussetzung in den Vordersatz. Eine mögliche Form ist \((P(1)\land\forall n\in\mathbb N\,(P(n)\Rightarrow P(n+1)))\Rightarrow\forall n\in\mathbb N\,P(n)\).
- Im Beweis über Minimum und Maximum zweier Ketten stehen vertauschte Ungleichungen und am Ende eines Falls ein falsches Maximum; im gesamten Min/Max-Abschnitt ist eine eigene Formelprüfung nötig.
- Die Schrödingergleichung und ihre Erläuterungen im Symbolteil brauchen eine gesonderte physikalische Prüfung; diese ist noch nicht erfolgt.
- Die jüngsten historischen Vorüberlegungen beziehen sich ausdrücklich auf eine Erinnerung an Wardhaughs Buch. Ihre sehr weitgehenden Formulierungen sind damit noch nicht belegt; das Buch wurde hier nicht abgeglichen.

Die meisten eindeutig falschen Formeln oben lassen sich örtlich korrigieren. Die aufwendigere gemeinsame Arbeit betrifft B1–B5: Dort muss geklärt werden, welchen Anspruch deine Begründung genau erhebt und welche Voraussetzungen sie dafür braucht.
