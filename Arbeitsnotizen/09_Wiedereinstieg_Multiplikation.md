# Ein konkreter Wiedereinstieg: die Faktoren vertauschen

Stand: 7. November 2026. Ergebnis von Arbeitspaket 8 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Diese Datei enthält einen Vorschlag und einen ausformulierten Schreibentwurf neben dem Manuskript. Die LyX-Quellen, Exporte und Sicherungen wurden nicht verändert. Fundstellen bezeichnen die heutigen LyX-Quellzeilen, keine Buchseiten.

Fortschreibung vom 11. November 2026: Der erste Haltepunkt bis einschliesslich `m·1=m` ist mit den ausgewählten örtlichen Additionskorrekturen inzwischen in beide Peano-Folgekapitel übernommen. Die Übernahme ist in [13 – Erste örtliche Übernahme ins Manuskript](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/13_Erste_oertliche_Uebernahme_ins_Manuskript.md) dokumentiert. Die beiden anschliessenden Multiplikationsbeweise bleiben als Arbeitspaket 13 zur Übernahme offen. Die folgenden ursprünglichen Fundstellen bezeichnen den Stand dieses Entwurfs vor der Übernahme.

## 1. Der kleine Anschluss

**Mein Vorschlag ist, unmittelbar nach Deiner Multiplikationsdefinition bis zum Satz `m·n=n·m` weiterzuschreiben und dort zunächst aufzuhören.** Dazu genügen zwei Hilfssätze und ein Satz mit jeweils einem vollständigen Induktionsbeweis. Damit lässt sich die im Symbolteil schon angesprochene Vertauschbarkeit der Faktoren tatsächlich begründen, statt sie nur anzukündigen.

Der Einfügeort liegt nach dem Definitionsabsatz [Zahlenteil 18843–18866](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18843), vor „Über die Anzahl der Begrüßungen“ bei 18868. Im zweiten, textgleichen Peano-Folgekapitel entspricht dem die [Definition 22058–22081](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22058), vor der Überschrift bei 22083. Das sind zwei mögliche Orte für denselben Entwurf. Eine Übernahme in beide Kapitel oder eine Zusammenführung der Kapitel ist damit nicht entschieden; deren Verhältnis ist in [Arbeitspaket 7](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/08_Manuskriptaufbau_und_technische_Altlasten.md) dokumentiert.

Der erste neue Satz `m·1=m` wäre bereits ein abgeschlossenes Stück für eine kurze Schreibsitzung. Die beiden folgenden Beweise sind vorbereitet, damit der nächste Anschluss schon greifbar ist. Distributivität und Assoziativität der Multiplikation bleiben für eine spätere Fortsetzung übrig.

## 2. Was der Entwurf voraussetzt

Der Entwurf benutzt Deine Festlegung `ℕ={1,2,…}` und genau Deine Rekursion **im ersten Faktor**:

\[
1\cdot n=n,\qquad (m+1)\cdot n=m\cdot n+n.
\]

Dabei wird die Multiplikation als eindeutig bestimmte Funktion von zwei natürlichen Zahlen in die natürlichen Zahlen verwendet. Für festes `n` beginnt ihr endlicher Aufbau mit `n` und setzt sich durch Addition von `n` fort. Dass dieser Aufbau eine Funktion für alle positiven natürlichen Zahlen liefert, gehört zur ausdrücklich vorausgesetzten Grundlage endlicher Rekursion. Die Eindeutigkeit folgt durch Induktion: Zwei solche Zuordnungen stimmen bei 1 überein und liefern aus gleichen bisherigen Werten gleiche Nachfolgerwerte. Diese Grundlage wird hier benannt; die bisherige Definitionsformel allein ist kein neuer Beweis des allgemeinen Rekursionssatzes.

Ausserdem werden Induktion ab 1, das Einsetzen gleicher Zahlen sowie Assoziativität und Kommutativität der **Addition** benutzt. Die Beweise der neuen Multiplikationssätze sind unter diesen Voraussetzungen geschlossen. Für die spätere Übernahme ins Skript sind insbesondere folgende örtlichen Arbeiten vorgemerkt:

| Voraussetzung | Vorliegende Grundlage und noch nachzuführende Arbeit |
| --- | --- |
| Endliche Ketten und Induktion | [Arbeitspaket 2, Abschnitte 1, 4 und 6](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/03_Begruendungskette_natuerliche_Zahlen.md): Kettengrundlage ausdrücklich nennen, Anfangsstücklemma und Minimumbeweis ergänzen, die ausgelassenen Induktionsschritte schliessen. |
| Addition ist assoziativ | [Arbeitspaket 5, Abschnitt 2](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md): Begründungszuordnung im ersten Beweis bzw. Schlussformel im direkten Kettenbeweis berichtigen. |
| Addition ist kommutativ | [Arbeitspaket 5, Abschnitt 3](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md): die dort dokumentierten falschen Zwischenformeln durch den vollständigen Ketten- oder Induktionsbeweis ersetzen. |

Zum Arbeiten am neuen Abschnitt können diese geprüften Voraussetzungen ausdrücklich festgehalten werden. Bei der späteren Übernahme müssen die einschlägigen Korrekturen mitgeführt werden, damit die Begründung auch im Manuskript durchgehend lesbar ist. Es ist dafür keine Neufassung aller abgeschlossenen Teile erforderlich.

## 3. Schreibentwurf unmittelbar nach der vorhandenen Definition

**Beginn des vorgeschlagenen Manuskripttexts.** Die folgende Ich-Form ist ein Formulierungsvorschlag im Anschluss an Deinen Text; sie gibt keine neuen persönlichen Äusserungen von Dir wieder.

### Was darf man mit den Faktoren machen?

Nun haben wir die Multiplikation definiert. Aber damit ist noch nicht gezeigt, dass wir mit ihr alles machen dürfen, was wir vom Rechnen her gewohnt sind. In der Definition wird der erste Faktor um eins vergrössert. Was passiert, wenn wir stattdessen den zweiten Faktor vergrössern? Und dürfen wir die beiden Faktoren vertauschen?

Ich möchte das in kleinen Schritten untersuchen. Dabei verwende ich die vollständige Induktion und die bereits behandelten Rechengesetze der Addition. Unsere natürlichen Zahlen beginnen weiterhin mit 1.

Zunächst noch zum Punkt zwischen den Symbolen: Bei \(m\cdot A\) steht rechts ein Grundsymbol, aus dem eine Kette gebildet wird. Bei \(m\cdot n\) stehen dagegen zwei natürliche Zahlen, und das Ergebnis ist wieder eine natürliche Zahl. Der Zusammenhang bleibt erhalten: Die Kette \((m\cdot n)\cdot A\) besteht aus \(m\) aneinandergehängten Blöcken \(n\cdot A\). Für \(m=1\) ist das die Definition. Bei jedem Nachfolgerschritt kommt wegen \((m+1)\cdot n=m\cdot n+n\) und der Additionsdefinition ein weiterer Block \(n\cdot A\) hinzu. Damit gilt diese Beschreibung nach vollständiger Induktion für alle \(m\).

So ist beispielsweise

\[
2\cdot3=1\cdot3+3=3+3.
\]

Die zugehörige Kette ist \((AAA)(AAA)\). Die Klammern zeigen hier nur die beiden Blöcke; sie gehören nicht zu den gezählten Grundsymbolen. Nun aber zurück zu den Zahlen.

### Hilfssatz: Die Eins als zweiter Faktor

Es sei \(m\in\mathbb N\). Dann gilt

\[
m\cdot1=m.
\]

**Beweis.** Dass \(1\cdot m=m\) gilt, steht bereits in der Definition. Hier steht die Eins jedoch auf der anderen Seite des Punkts. Ich möchte deshalb nicht einfach die Faktoren vertauschen, sondern die Behauptung durch vollständige Induktion über \(m\) beweisen.

Für \(m=1\) gilt nach der Definition \(1\cdot1=1\). Damit ist der Induktionsanfang erledigt.

Es sei nun \(m\) eine beliebige natürliche Zahl, für die \(m\cdot1=m\) gilt. Dann folgt

\[
\begin{aligned}
(m+1)\cdot1
  &=m\cdot1+1 &&\text{(Definition der Multiplikation)}\\
  &=m+1 &&\text{(Induktionsannahme).}
\end{aligned}
\]

Die Behauptung gilt somit auch für den Nachfolger von \(m\), also nach vollständiger Induktion für jede natürliche Zahl \(m\).

### Hilfssatz: Den zweiten Faktor um eins vergrössern

Es seien \(m,n\in\mathbb N\). Dann gilt

\[
m\cdot(n+1)=m\cdot n+m.
\]

**Beweis.** Hier muss ich aufpassen: In der Definition steht der Nachfolger im ersten Faktor. Dort darf ich also nicht einfach \(m\cdot(n+1)\) durch \(m\cdot n+m\) ersetzen. Das ist gerade die Behauptung, die erst bewiesen werden soll.

Ich halte \(n\) beliebig, aber fest und führe die vollständige Induktion über \(m\).

Für \(m=1\) gilt

\[
1\cdot(n+1)=n+1=1\cdot n+1.
\]

Beide Gleichheiten folgen aus der Definition der Multiplikation. Damit stimmt die Behauptung für \(m=1\).

Nun gelte für eine beliebige natürliche Zahl \(m\) die Induktionsannahme

\[
m\cdot(n+1)=m\cdot n+m.
\]

Für ihren Nachfolger ergibt sich:

\[
\begin{aligned}
(m+1)\cdot(n+1)
 &=m\cdot(n+1)+(n+1)
   &&\text{(Definition)}\\
 &=(m\cdot n+m)+(n+1)
   &&\text{(Induktionsannahme)}\\
 &=m\cdot n+\bigl((m+n)+1\bigr)
   &&\text{(Assoziativität der Addition)}\\
 &=m\cdot n+\bigl((n+m)+1\bigr)
   &&\text{(Kommutativität der Addition)}\\
 &=(m\cdot n+n)+(m+1)
   &&\text{(Assoziativität der Addition)}\\
 &=\bigl((m+1)\cdot n\bigr)+(m+1)
   &&\text{(Definition).}
\end{aligned}
\]

Das ist genau die Behauptung für \(m+1\). Nach vollständiger Induktion gilt sie für alle natürlichen Zahlen \(m\). Da \(n\) beliebig gewählt war, gilt sie für alle \(m,n\in\mathbb N\).

Bei diesem Beweis habe ich Summanden vertauscht und Klammern in Summen verschoben. Faktoren habe ich noch keine vertauscht.

### Satz: Die Faktoren dürfen vertauscht werden

Es seien \(m,n\in\mathbb N\). Dann gilt

\[
m\cdot n=n\cdot m.
\]

**Beweis.** Ich halte wieder \(n\) beliebig fest und führe die vollständige Induktion über \(m\).

Für \(m=1\) gilt

\[
1\cdot n=n=n\cdot1.
\]

Die erste Gleichheit ist die Definition; die zweite folgt aus dem ersten Hilfssatz.

Nun sei \(m\cdot n=n\cdot m\) für eine beliebige natürliche Zahl \(m\) richtig. Dann gilt

\[
\begin{aligned}
(m+1)\cdot n
  &=m\cdot n+n &&\text{(Definition)}\\
  &=n\cdot m+n &&\text{(Induktionsannahme)}\\
  &=n\cdot(m+1) &&\text{(zweiter Hilfssatz).}
\end{aligned}
\]

Damit ist auch der Induktionsschritt erbracht. Weil \(n\) beliebig war, gilt die Behauptung für alle natürlichen Zahlen \(m\) und \(n\). Die Multiplikation ist also kommutativ.

Nun darf ich beispielsweise \(2\cdot3=3\cdot2\) schreiben. Die Definition hat zunächst zwei Dreierblöcke beziehungsweise drei Zweierblöcke geliefert. Dass die zugehörigen Zahlen gleich sind, ist jetzt auch allgemein begründet.

**Ende des vorgeschlagenen Manuskripttexts.** Hier liegt ein sinnvoller Haltepunkt für diesen Wiedereinstieg.

## 4. Falls zuerst die Kettengrundlage ausgesprochen werden soll

Soll der Wiedereinstieg lieber an der ausdrücklich notierten Unsicherheit bei der Vergleichbarkeit ansetzen, ist ein kurzer Einschub vor den Kettenbeweisen eine Alternative. Ein möglicher Wortlaut lautet:

> Ich lege ein festes, nichtleeres Grundsymbol und eine feste Zerlegung in solche Grundsymbole zugrunde. Betrachtet werden genau die nichtleeren Ketten, die daraus durch endliches Anhängen entstehen. Das Anhängen und das Verketten solcher Ketten liefern wieder solche Ketten; ihre Gleichheit richtet sich nach der Folge der Grundsymbole. Beim wiederholten Entfernen des letzten Grundsymbols gelangt man schliesslich zum einzelnen Grundsymbol. Aussagen über diese Ketten darf ich anhand ihres endlichen Aufbaus begründen: beim Grundsymbol anfangen und zeigen, dass die Aussage beim Anhängen erhalten bleibt. Damit setze ich eine Grundlage über endliche Ketten voraus. Ich möchte sichtbar machen, wie die Zahleneigenschaften damit zusammenhängen. Eine Herleitung ohne jede solche Voraussetzung ist damit nicht behauptet.

Dieser Einschub legt die Rolle der endlichen Ketten und der strukturellen Induktion offen. Das in [Arbeitspaket 2, Abschnitt 4](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/03_Begruendungskette_natuerliche_Zahlen.md) formulierte Lemma über die endlich vielen Anfangsstücke und der reparierte Minimumbeweis müssen danach weiterhin ausgeführt werden. Der Absatz allein ersetzt diese Beweise nicht.

## 5. Was nach diesem kleinen Abschnitt noch offen bleibt

Fortschreibung vom 8. November 2026: Die folgende Fortsetzung ist inzwischen als Arbeitspaket 9 in [10 – Distributivität und Assoziativität](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/10_Distributivitaet_und_Assoziativitaet.md) vollständig ausgearbeitet. Die Tabelle hält den ursprünglichen Anschlussplan fest.

Für einen späteren Ausbau liegt folgende Reihenfolge nahe; sie gehört noch nicht zum obigen Manuskriptentwurf:

| Fortsetzung | Passender Beweisweg |
| --- | --- |
| `(a+b)·c=a·c+b·c` | Induktion über `b`, bei festem `a,c`. Anfang `b=1` durch die Rekursion. Im Schritt `(a+(b+1))·c=((a+b)+1)·c=(a+b)·c+c=(a·c+b·c)+c=a·c+(b+1)·c`. Hier werden nur die Rekursion, die Additionsgesetze und die Induktionsannahme gebraucht. |
| `a·(b+c)=a·b+a·c` | Nach der ersten Distributivität folgt mit dem oben bewiesenen Vertauschen der Faktoren: `a·(b+c)=(b+c)·a=b·a+c·a=a·b+a·c`. |
| `(a·b)·c=a·(b·c)` | Induktion über `a`, bei festem `b,c`. Anfang `a=1` durch die Definition. Im Schritt liefert die erste Distributivität `((a+1)·b)·c=(a·b+b)·c=(a·b)·c+b·c=a·(b·c)+b·c=(a+1)·(b·c)`. |

Der obige Entwurf begründet noch nicht die gesamte Rechnung der anschliessenden Handschlagaufgabe. Dort werden zusätzlich Distributivität, Subtraktion und Bruchrechnung verwendet; die örtliche Korrektur der verlorenen Summe und diese Voraussetzungen sind in [Arbeitspaket 5, Abschnitt 6](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md) dokumentiert. Auch die Nullfälle der logischen Rechendarstellung liegen ausserhalb des hier behandelten positiven Zahlbereichs.

## 6. Fachliche Kontrolle und Abschluss

Die Definition und beide möglichen Anschlussstellen wurden an der aktuellen LyX-Quelle abgeglichen. Die Beweise wurden auf Induktionsvariable, festgehaltene Parameter, Anfang bei 1 und die Rechtfertigung jeder Umformung geprüft. Ihre Abhängigkeiten sind:

- `m·1=m`: Rekursion und Induktion.
- `m·(n+1)=m·n+m`: Rekursion, Induktion sowie Assoziativität und Kommutativität der Addition.
- `m·n=n·m`: Rekursion, Induktion und die beiden Hilfssätze.

Insbesondere wird im zweiten Hilfssatz weder Multiplikationskommutativität noch eine Distributivregel vorausgesetzt. Die spätere Assoziativität der Multiplikation wird in keinem der drei Beweise benutzt. Die Kettenbeschreibung im Einstieg wird unmittelbar aus Rekursion und Addition induktiv begründet. Diese Kontrolle ist eine mathematische Durchsicht des Entwurfs, keine maschinelle Formalisierung und kein neuer LyX-/PDF-Bau.

**Arbeitspaket 8 ist damit abgeschlossen:** Ein kleiner Anschluss mit genauem Ort, benannten Voraussetzungen, ausformulierten Beweisen und einem Haltepunkt liegt vor; ebenso eine kurze Alternative zur Kettengrundlage. Alle acht bisher nummerierten Arbeitspakete sind dokumentiert bearbeitet. Die spätere Übernahme der Korrekturen und des Schreibentwurfs ins Manuskript bleibt offen. Für die erste eigene Schreibsitzung genügt der Einstieg bis einschliesslich `m·1=m`.
