# Die Multiplikation weiterführen: Summen und Klammern

Stand: 8. November 2026. Ergebnis von Arbeitspaket 9 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Die ursprünglichen acht Arbeitspakete waren bereits abgeschlossen. Dieses Paket arbeitet die in [09 – Wiedereinstieg Multiplikation, Abschnitt 5](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/09_Wiedereinstieg_Multiplikation.md) dokumentierte Fortsetzung aus: beide Distributivgesetze und die Assoziativität der Multiplikation. Der Schreibentwurf steht neben dem Manuskript; LyX-Quellen, Exporte und Sicherungen wurden nicht verändert.

## 1. Anschlussstelle und Voraussetzungen

Der folgende Text schliesst unmittelbar an den Kommutativitätsbeweis des vorherigen Schreibentwurfs an. Bei einer späteren Übernahme stehen beide Entwürfe gemeinsam nach der Multiplikationsdefinition und vor „Über die Anzahl der Begrüßungen“: [Zahlenteil 18843–18868](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18843), beziehungsweise [22058–22083](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22058) im zweiten Peano-Folgekapitel. Die Definitionen und diese Anschlussstellen wurden an der aktuellen Quelle abgeglichen. Zeilenangaben bezeichnen LyX-Quellzeilen, keine Buchseiten. Die Entscheidung über das Verhältnis der beiden Kapitel bleibt offen.

Weiterhin gilt Deine Festlegung \(\mathbb N=\{1,2,\ldots\}\). Die Multiplikation ist die durch endliche Rekursion bestimmte Funktion \(\mathbb N\times\mathbb N\to\mathbb N\) mit

\[
1\cdot n=n,\qquad (m+1)\cdot n=m\cdot n+n.
\]

Benutzt werden vollständige Induktion ab 1, Einsetzen gleicher Zahlen, die Additionsgesetze und die im vorherigen Entwurf bewiesene Multiplikationskommutativität. Die Ketten- und Rekursionsgrundlage sowie die noch in die Quellen zu übernehmenden örtlichen Korrekturen der Additionsbeweise bleiben genau wie in [09, Abschnitt 2](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/09_Wiedereinstieg_Multiplikation.md) vorausgesetzt. Der neue Entwurf behebt diese früheren Manuskriptstellen nicht selbst.

Die drei neuen Beweise haben folgende Reihenfolge:

| Satz | Unmittelbar benutzte Grundlagen |
| --- | --- |
| \((a+b)\cdot c=a\cdot c+b\cdot c\) | Rekursion im ersten Faktor, Assoziativität der Addition, Induktion über \(b\). |
| \(a\cdot(b+c)=a\cdot b+a\cdot c\) | Der erste neue Satz und Kommutativität der Multiplikation aus dem vorherigen Entwurf. |
| \((a\cdot b)\cdot c=a\cdot(b\cdot c)\) | Rekursion, der erste neue Satz, Induktion über \(a\). |

Insbesondere benötigt der erste Satz noch keine Assoziativität oder Kommutativität der Multiplikation. Auch der dritte Satz kann ohne die zweite Distributivregel bewiesen werden.

## 2. Schreibentwurf: Was geschieht mit einer Summe?

**Beginn des vorgeschlagenen Manuskripttexts.** Die Ich-Form ist ein Formulierungsvorschlag im Anschluss an den vorhandenen Text, keine neue persönliche Äusserung von Dir.

Die Faktoren dürfen wir nun vertauschen. Wie steht es mit einer Summe, die als Faktor vorkommt? Bei der Definition haben wir zum ersten Faktor jeweils eins hinzugefügt. Jetzt möchte ich statt der Eins eine beliebige natürliche Zahl hinzufügen.

### Satz: Eine Summe im ersten Faktor

Es seien \(a,b,c\in\mathbb N\). Dann gilt

\[
(a+b)\cdot c=a\cdot c+b\cdot c.
\]

**Beweis.** Ich halte \(a\) und \(c\) beliebig, aber fest. Über \(b\) führe ich die vollständige Induktion.

Für \(b=1\) ergibt die Definition:

\[
\begin{aligned}
(a+1)\cdot c
 &=a\cdot c+c &&\text{(Rekursion)}\\
 &=a\cdot c+1\cdot c &&\text{(weil }1\cdot c=c\text{).}
\end{aligned}
\]

Das ist die Behauptung für \(b=1\).

Für eine beliebige natürliche Zahl \(b\) gelte nun

\[
(a+b)\cdot c=a\cdot c+b\cdot c.
\]

Dann folgt für ihren Nachfolger:

\[
\begin{aligned}
\bigl(a+(b+1)\bigr)\cdot c
 &=\bigl((a+b)+1\bigr)\cdot c
   &&\text{(Assoziativität der Addition)}\\
 &=(a+b)\cdot c+c
   &&\text{(Rekursion)}\\
 &=(a\cdot c+b\cdot c)+c
   &&\text{(Induktionsannahme)}\\
 &=a\cdot c+(b\cdot c+c)
   &&\text{(Assoziativität der Addition)}\\
 &=a\cdot c+(b+1)\cdot c
   &&\text{(Rekursion).}
\end{aligned}
\]

Damit gilt die Behauptung nach vollständiger Induktion für alle \(b\in\mathbb N\). Weil auch \(a\) und \(c\) beliebig waren, ist der Satz für alle drei natürlichen Zahlen bewiesen.

Die Regel lässt sich beispielsweise so lesen: Fünf Dreierblöcke können in zwei Dreierblöcke und drei Dreierblöcke aufgeteilt werden. In Zahlen steht dafür

\[
(2+3)\cdot3=2\cdot3+3\cdot3.
\]

### Satz: Eine Summe im zweiten Faktor

Es seien \(a,b,c\in\mathbb N\). Dann gilt auch

\[
a\cdot(b+c)=a\cdot b+a\cdot c.
\]

**Beweis.** Dafür brauche ich keine neue Induktion. Ich darf die Faktoren bereits vertauschen und habe die Regel für eine Summe im ersten Faktor gerade bewiesen. Deshalb gilt

\[
\begin{aligned}
a\cdot(b+c)
 &=(b+c)\cdot a &&\text{(Kommutativität der Multiplikation)}\\
 &=b\cdot a+c\cdot a &&\text{(vorheriger Satz)}\\
 &=a\cdot b+a\cdot c &&\text{(Kommutativität der Multiplikation).}
\end{aligned}
\]

Auch \(b+c\) ist eine natürliche Zahl; die Kommutativität darf deshalb schon auf die erste Zeile angewendet werden.

Diese beiden Regeln heissen Distributivgesetze: Die Multiplikation verteilt sich über eine Summe. Man kann sie von links nach rechts zum Ausmultiplizieren lesen. Liest man sie von rechts nach links, wird ein gemeinsamer Faktor ausgeklammert. Dafür ist kein weiterer Satz erforderlich, denn eine Gleichheit gilt in beiden Richtungen.

## 3. Schreibentwurf: Wie dürfen drei Faktoren geklammert werden?

Die Reihenfolge zweier Faktoren dürfen wir vertauschen, und mit Summen können wir nun ebenfalls umgehen. Bleibt die Frage nach drei Faktoren. Kommt dasselbe heraus, wenn wir zuerst die ersten beiden oder zuerst die letzten beiden miteinander multiplizieren?

### Satz: Assoziativität der Multiplikation

Es seien \(a,b,c\in\mathbb N\). Dann gilt

\[
(a\cdot b)\cdot c=a\cdot(b\cdot c).
\]

**Beweis.** Diesmal halte ich \(b\) und \(c\) beliebig, aber fest und führe die vollständige Induktion über \(a\).

Für \(a=1\) gilt

\[
(1\cdot b)\cdot c=b\cdot c=1\cdot(b\cdot c).
\]

Beide Gleichheiten folgen aus \(1\cdot n=n\). Da \(b\cdot c\) wieder eine natürliche Zahl ist, darf ich diese Definition auch für \(n=b\cdot c\) verwenden.

Für eine beliebige natürliche Zahl \(a\) gelte nun die Induktionsannahme

\[
(a\cdot b)\cdot c=a\cdot(b\cdot c).
\]

Dann folgt:

\[
\begin{aligned}
\bigl((a+1)\cdot b\bigr)\cdot c
 &=(a\cdot b+b)\cdot c
   &&\text{(Rekursion für }(a+1)\cdot b\text{)}\\
 &=(a\cdot b)\cdot c+b\cdot c
   &&\text{(Distributivgesetz für den ersten Faktor)}\\
 &=a\cdot(b\cdot c)+b\cdot c
   &&\text{(Induktionsannahme)}\\
 &=(a+1)\cdot(b\cdot c)
   &&\text{(Rekursion mit zweitem Faktor }b\cdot c\text{).}
\end{aligned}
\]

Im zweiten Schritt habe ich beim Distributivgesetz die natürlichen Zahlen \(a\cdot b\) und \(b\) als Summanden eingesetzt. Im letzten Schritt steht die Definitionsgleichung von rechts nach links. Dort wird keine Klammer in einem Produkt verschoben.

Damit gilt die Behauptung für \(a+1\) und nach vollständiger Induktion für alle \(a\in\mathbb N\). Weil \(b\) und \(c\) beliebig waren, ist die Assoziativität der Multiplikation bewiesen.

Nun kann ich bei drei Faktoren die Klammern weglassen und \(a\cdot b\cdot c\) schreiben: Die beiden möglichen Klammerungen liefern denselben Wert. Beispielsweise ist

\[
(2\cdot3)\cdot4=2\cdot(3\cdot4)=24.
\]

Bei den Distributivgesetzen muss die Summe dagegen weiterhin erkennbar bleiben: \(a\cdot(b+c)\) bedeutet, dass die ganze Summe als zweiter Faktor eingesetzt wird.

**Ende des vorgeschlagenen Manuskripttexts.** Nach den beiden Distributivgesetzen ist bereits ein kleiner Haltepunkt erreicht; mit dem dritten Satz ist auch das Umklammern von drei Faktoren begründet.

## 4. Was damit erreicht ist und was als Nächstes anschliesst

Zusammen mit dem vorherigen Entwurf sind nun die Einsregeln, die Nachfolgerregel im zweiten Faktor, die Kommutativität, beide Distributivgesetze und die Assoziativität für die positiven natürlichen Zahlen ausgearbeitet. Die Regeln werden aus der festgehaltenen Rekursion und den benannten Grundlagen hergeleitet; sie sind keine zusätzlichen Definitionen.

Die anschliessende Handschlagaufgabe benutzt darüber hinaus Subtraktion, Bruchrechnung und Teilbarkeit durch 2. Die in [06 – Rechnen und Zahlbereiche, Abschnitt 6](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md) dokumentierte örtliche Korrektur bei [Zahlen 19118](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19118), wiederholt bei [22333](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22333), bleibt erforderlich. Der neue Entwurf führt diese zusätzlichen Operationen nicht ein.

Fortschreibung vom 10. November 2026: Der folgende Anschluss zu Ordnung und Kürzbarkeit ist inzwischen als Arbeitspaket 10 in [11 – Multiplikation, Ordnung und Kürzbarkeit](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/11_Multiplikation_Ordnung_und_Kuerzbarkeit.md) vollständig ausgearbeitet. Die nachfolgende Skizze hält den ursprünglichen Anschlussplan fest.

Der nächste abgegrenzte Anschluss ist **Multiplikation, Ordnung und Kürzbarkeit positiver Faktoren**. Dieser Bedarf und der Beweisansatz sind bereits in [06, Abschnitt 4](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md) dokumentiert: Aus \(b=a+k\) mit \(k\in\mathbb N\) folgt \(b\cdot c=a\cdot c+k\cdot c>a\cdot c\). Aus strenger Ordnungserhaltung lässt sich anschliessend mittels Vergleichbarkeit die Kürzungsregel herleiten. Dafür sind die Ordnungsgrundlage und der positive Rest ausdrücklich zu verwenden; eine vorherige Division wird nicht benötigt. Das ist in der Aufgabenliste als Arbeitspaket 10 vorgemerkt und hier noch nicht ausgearbeitet. Die spätere Erweiterung auf \(\mathbb N_0\) und die Einführung von Subtraktion und Division bleiben weitere Schritte.

## 5. Fachliche Kontrolle und Abschluss

Die Durchsicht hat bei jedem Induktionsbeweis die Variable, die festgehaltenen Parameter, den Anfang bei 1 und die genau einmal benutzte Induktionsannahme geprüft. Jeder Rekursionsschritt vergrössert den **ersten** Faktor; im Assoziativitätsbeweis wird als zweiter Faktor auch die bereits natürliche Zahl \(b\cdot c\) eingesetzt. Die Distributivregel wird dort auf die Summe \(a\cdot b+b\) angewendet, ohne die noch zu beweisende Produktklammerung vorauszusetzen. Beide Endformeln entsprechen jeweils der Behauptung für den Nachfolger.

Ergänzend wurden beide Distributivgleichungen und die Assoziativitätsgleichung für sämtliche \(1\leq a,b,c\leq12\) durchgerechnet, insgesamt 1’728 Zahlentripel mit jeweils drei Gleichungen. Die dazu verwendete Multiplikation wurde durch wiederholte Addition gemäss der Rekursion im ersten Faktor aufgebaut. Die endlichen Gegenproben sind eine zusätzliche Rechenkontrolle; der allgemeine Nachweis sind die ausgeschriebenen Beweise. Es wurde keine maschinelle Formalisierung und kein neuer LyX-/PDF-Bau vorgenommen.

**Arbeitspaket 9 ist abgeschlossen:** Die zuvor skizzierte Fortsetzung liegt als ausformulierter Schreibentwurf mit Anschlussstelle, Voraussetzungen, begründeten Beweisschritten und Haltepunkten vor. Die Übernahme dieses Entwurfs und der früher dokumentierten Korrekturen ins Manuskript bleibt offen.
