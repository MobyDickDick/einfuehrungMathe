# Aussagenbegriff, Selbstbezug und Widerspruchsfreiheit

Stand: 3. November 2026. Ergebnis von Arbeitspaket 3 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Grundlage sind die aktuell eingebundenen LyX-Quellen, insbesondere `Teil_Symbole.lyx`, `Teil_Logik.lyx` und die ergänzend herangezogene Delta-Definition in `Restposten.lyx`. Zeilenangaben bezeichnen Quellzeilen, keine Buchseiten. Die Prüfung und die Ersatzvorschläge stehen neben dem Manuskript; dieses wurde nicht verändert.

## 1. Ergebnis und Reichweite

**Die Sorge hinter dem wiederholten Mantra ist berechtigt: Beim Rechnen mit Aussagen muss feststehen, was ihre Zeichen jeweils bedeuten. „Widerspruchsfreiheit“ allein beschreibt diese Voraussetzung aber nicht ausreichend.** Im Text werden wechselnder Bezug, unerfüllbare Bedingungen, Selbstbezug, fehlendes Wissen und zirkuläre Begründungen teilweise unter demselben Begriff behandelt. Das sind verschiedene Probleme und verlangen verschiedene Antworten.

Das Lage-Beispiel kann erhalten bleiben. Es veranschaulicht, wie das Versetzen einer sprachlichen Formulierung ihren Inhalt verändern kann. Die Folgerung, damit sei eine innere Widersprüchlichkeit der klassischen Aussagenlogik gezeigt, trägt es nicht. Auch die Beispiele mit Barbier, Verbotstafel und Wind/Wolken zeigen keine Widersprüchlichkeit der Schlussregeln. Ein zusätzlicher erheblicher Fehler liegt im Negationskapitel: Nicht zu wissen, ob eine Aussage wahr ist, berechtigt nicht dazu, ihre Negation zu behaupten.

Geprüft wurden die tragenden Begriffsbestimmungen, die einschlägigen Beispiele und die daraus gezogenen Behauptungen über Grenzen der Logik. **Dies ist keine Einzelprüfung sämtlicher Wahrheitstabellen und Beweise des umfangreichen Logikteils.** Die systematische Prüfung von Quantoren und Mengenlehre bleibt Arbeitspaket 4; physikalische, historische und psychologische Sachbehauptungen bleiben Arbeitspaket 6. Die hier nötigen Unterscheidungen betreffen bereits die Aussagenlogik.

## 2. Fünf Ebenen, die auseinandergehalten werden müssen

**Fundstellen:** [Metasymbole, Symbolteil 1395–1428](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:1395); [Aussagendefinition, Logikteil 554–643](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:554).

| Ebene | Beispiel | Was dabei festzuhalten ist |
| --- | --- | --- |
| Symbol als vereinbartes Zeichen | der Buchstabe `A` | Seine Gestalt allein legt den bezeichneten Inhalt nicht fest. |
| Symbolvorkommen | das erste und das zweite `A` in `A∧A` | Zwei konkrete Stellen können dasselbe Zeichen verwenden. Im formalen Ausdruck müssen sie dieselbe Interpretation erhalten. |
| Symbolkette / Formel | die Zeichenfolge `A∧B` | Eine beliebige Kette ist noch keine wohlgeformte Formel. Eine Formel ist noch keine Behauptung, dass sie wahr sei. |
| Aussageinhalt | dass an einem bestimmten Ort zu einem bestimmten Zeitpunkt Menschen leben | Derselbe Inhalt kann unterschiedlich geschrieben werden; dieselbe Zeichenkette kann bei anderem Kontext etwas anderes ausdrücken. |
| Kontext / Interpretation | Schreibstelle, Zeit, Sprecher, Bezug von „vorher“; im Kalkül eine Wahrheitswertbelegung | Kontextabhängige Ausdrücke brauchen festgelegte Bezüge, bevor ihre Wahrheitswerte verglichen werden. |

Die eigene Festlegung „Aussagen sind Aneinanderreihungen von Symbolen“ kann als weiter Sprachgebrauch bestehen bleiben. Für die spätere klassische Wahrheitslogik muss dann eine engere Klasse abgegrenzt werden: Ausdrücke mit bestimmtem Aussageinhalt, denen unter der betrachteten Interpretation genau einer der beiden Wahrheitswerte zukommt. Fragen, Befehle und unvollständige Satzstücke erhalten durch ihre blosse Schriftgestalt keinen solchen Wahrheitswert. Ein einzelnes Zeichen kann dagegen einen ganzen wahren Inhalt vertreten: Wird `d` als Abkürzung für `1=1` vereinbart, vertritt es eine wahre Aussage. Die Behauptung [bei 618–619](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:618), ein einzelnes Symbol könne wohl nie eine wahre Aussage bilden, ist deshalb zu stark. Eine Beschränkung auf mehrgliedrige Schreibweisen wäre eine eigene Namenskonvention, keine Eigenschaft der Wahrheit.

Zur begrifflichen Orientierung: Die [Logic Notes der ANU, „Sentence, Statement, Proposition“](https://users.cecs.anu.edu.au/~jks/LogicNotes/glossary/g_sentence.html), unterscheiden sprachlichen Satz, wahrheitsfähige Aussage und Inhalt und erläutern ausdrücklich das Festhalten indexikalischer Bezüge. Die [Darstellung „Use and mention“ in forall x: Calgary](https://forallx.openlogicproject.org/html/Ch8.html) trennt die Verwendung eines Ausdrucks vom Sprechen über ihn. Die obige Zuordnung zu den Manuskriptstellen ist die hiesige Analyse.

**Örtlicher Ergänzungsvorschlag:** „Mit Aussage meine ich zunächst weit gefasst eine Symbolkette. Für die folgenden Wahrheitsverknüpfungen betrachten wir jedoch nur Aussagen, deren Inhalt unter der jeweiligen Interpretation festliegt und entweder wahr oder nicht wahr ist. Ob wir wissen, welcher Fall zutrifft, ist eine andere Frage.“ Das präzisiert die Grundlage, ohne den weiten Ausgangsbegriff zu verbieten.

## 3. Das Lage-Beispiel: Was es tatsächlich zeigt

**Fundstellen:** [Kommutativitätssatz 79752–79859](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:79752); [Lage-Beispiel 80851–81047](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:80851); vorweggenommene Folgerung [2010–2023](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:2010).

Im Manuskript steht `A` für „Menschen leben“. `B` besagt, dass vorher die Aussage mit dem Symbol `A`, gefolgt von einem Konjunktionssymbol, hingeschrieben wurde. Das ist die geprüfte Fassung. Die in der früheren Zusammenfassung erwähnte Rechts-links-Fassung ist hier nicht als vollständiger eigener Text dokumentiert und wird nicht an ihre Stelle gesetzt.

Für die beabsichtigte Gegenüberstellung muss „vorher“ noch präzisiert werden: Gemeint sei **unmittelbar zuvor innerhalb des jeweils betrachteten Ausdrucks**. Bei einem beliebigen früheren Vorkommen im gesamten Dokument wäre auch das `B` in der später abgedruckten Zeile `B∧A` möglicherweise wahr: Auf derselben Seite steht ja schon `A∧B`. Die unpräzisierte Lesart garantiert den behaupteten Wahrheitswertunterschied somit noch nicht.

Unter der präzisierten Lesart funktioniert die sprachliche Beobachtung. Halten wir den Inhalt von `A` wahr und bezeichnen wir die beiden Schreibkontexte mit `c₁` und `c₂`, ergibt sich:

| Ausdruck als neu ausgewerteter Text | Inhalt von `B` an dieser Stelle | Wahrheitswert der Konjunktion |
| --- | --- | --- |
| `A∧B` im Kontext `c₁` | Vor diesem Vorkommen steht innerhalb der Zeile `A∧`: wahr | wahr |
| `B∧A` im Kontext `c₂` | Vor diesem Vorkommen steht innerhalb der Zeile kein `A∧`: nicht wahr | nicht wahr |

Formal werden also `A∧B[c₁]` und `B[c₂]∧A` verglichen. **Das Umstellen der Schriftstücke samt erneuter Auswertung ihres Lagebezugs ist eine andere Operation als das Vertauschen zweier festgehaltener Aussageinhalte.** Wird stattdessen `B[c₁]` festgehalten, sind `A∧B[c₁]` und `B[c₁]∧A` beide wahr. Ebenso sind bei festem `B[c₂]` beide Reihenfolgen nicht wahr.

Die klassische Regel lässt sich unabhängig vom Inhalt vollständig nachrechnen:

| A | B | A∧B | B∧A |
| --- | --- | --- | --- |
| nicht wahr | nicht wahr | nicht wahr | nicht wahr |
| nicht wahr | wahr | nicht wahr | nicht wahr |
| wahr | nicht wahr | nicht wahr | nicht wahr |
| wahr | wahr | wahr | wahr |

Dabei werden beide Seiten mit derselben Belegung ausgewertet. Diese Semantik mit einer festen Zuordnung der atomaren Aussagen zu Wahrheitswerten wird in [Poole/Mackworth, Abschnitt 5.1.2](https://www.cs.ubc.ca/~poole/aibook/2e/html2e/ArtInt2e.Ch5.S1.SS2.html) explizit definiert. Die Anwendung auf die beiden Schreibkontexte oben ist eine eigene Rekonstruktion des Beispiels.

**Befund:** Die Beobachtung über Lageabhängigkeit ist tragfähig; die Folgerung [81040–81045](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:81040), die vorgestellte Logik sei deshalb nicht vollständig widerspruchsfrei, ist nicht begründet. Der eigene Name „topologische Widersprüchlichkeit“ kann als Bezeichnung dieses Beispiels erläutert werden, sollte aber nicht den Eindruck eines nachgewiesenen logischen Widerspruchs oder eines hier bewiesenen Satzes der mathematischen Topologie erwecken.

**Kleiner Ersatz für die Schlussfolgerung:** „Dieses Beispiel zeigt, dass wir beim Vertauschen von Schriftstücken unbemerkt ihren Inhalt verändern können. Für den Kommutativitätssatz müssen dieselben Aussageinhalte festgehalten werden. Mein wiederholter Hinweis soll uns daran erinnern, solche Voraussetzungen vor der Anwendung zu prüfen.“

## 4. Vier verschiedene Bedeutungen von Widerspruchsfreiheit

**Fundstellen:** [der ausdrückliche „Zauberspruch“, Symbolteil 3591–3618](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:3591); [Definition von Ω, Logikteil 1376–1401](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:1376); [erneute Erklärung 4812–4836](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:4812).

| Gemeintes Problem | Passende Anforderung | Reicht „widerspruchsfrei“ dafür? |
| --- | --- | --- |
| Der Bezug wechselt beim Umstellen oder Einsetzen | Feste Interpretation und festgelegter Umgang mit Kontext | Nein. Zwei verschiedene kontextuelle Inhalte können problemlos verschiedene Wahrheitswerte haben. |
| Eine einzelne Formel kann niemals wahr sein | Erfüllbarkeit dieser Formel | Das ist eine echte semantische Eigenschaft; eine unerfüllbare Formel bleibt trotzdem ein zulässiger Untersuchungsgegenstand. |
| Mehrere Voraussetzungen können nicht zusammen wahr sein | Gemeinsame Erfüllbarkeit des ganzen Voraussetzungssystems | Einzelne Erfüllbarkeit genügt nicht: `P` und `¬P` sind einzeln erfüllbar, zusammen nicht. |
| Eine Theorie beweist sowohl eine Formel als auch deren Negation | Widerspruchsfreiheit relativ zu ihren Axiomen und Schlussregeln | Das betrifft eine Theorie, nicht die blosse Gestalt eines Symbols. |

Die [semantischen Begriffe in forall x: Calgary, Kapitel 12](https://forallx.openlogicproject.org/html/Ch12.html), trennen Tautologie, Kontradiktion, Äquivalenz, Erfüllbarkeit und Folgerung. Insbesondere ist eine Kontradiktion eine Formel, die bei jeder Belegung nicht wahr ist. Daraus folgt keine Unzulässigkeit ihrer Untersuchung.

Ein Beispiel macht die Konsequenz für das Mantra sichtbar: Setze in die Kommutativitätsregel `A=P` und `B=¬P` ein. Die Konjunkte können nicht gemeinsam wahr sein. Trotzdem gilt

\[
(P\land\neg P)\leftrightarrow(\neg P\land P).
\]

Beide Seiten sind stets nicht wahr, ihre Äquivalenz ist stets wahr. Gegenseitige Verträglichkeit der eingesetzten Aussagen ist für dieses Gesetz also nicht nötig. Würden nur gemeinsam erfüllbare Einsetzungen zugelassen, wäre der Satz unnötig eingeschränkt; die übrigen Wahrheitstafelfälle würden dadurch nicht falsch.

### Warum Ω in der vorhandenen Form noch nicht ausreicht

Die Wendung „bezüglich den anderen Aussagen widerspruchsfrei“ macht die Zulässigkeit von einer nicht benannten Umgebung abhängig. Sollen alle Elemente von Ω gemeinsam erfüllbar sein, kann Ω beispielsweise nicht zugleich `P` und `¬P` enthalten. Sollen nur einzeln erfüllbare Formeln dazugehören, sind zwar beide zugelassen, ihre Konjunktion aber nicht. Eine solche Klasse ist unter den später benutzten Verknüpfungen nicht abgeschlossen.

Ausserdem kann eine aus Ω ausgeschlossene Formel nicht dadurch wieder Element einer Teilmenge der nicht wahren Aussagen **innerhalb von Ω** werden, dass man sie als nicht wahr bezeichnet. Genau dies bleibt [bei 4812–4836](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:4812) ungeklärt.

**Reparaturvorschlag:** Für die Aussagenlogik eine festgelegte formale Sprache mit wohlgeformten Formeln wählen und ihre Gesamtheit mit Ω bezeichnen. Auch Kontradiktionen gehören dazu. Wahr oder nicht wahr ist eine Formel unter einer Belegung `v`; dafür kann man `W_v={F∈Ω | v(F)=1}` verwenden. Gemeinsame Erfüllbarkeit wird gesondert von einem gewählten Voraussetzungssystem verlangt. Soll Ω stattdessen bei seinem bisherigen eingeschränkten Sinn bleiben, braucht die Gesamtheit der untersuchten Formeln einen anderen Namen und die fehlenden Abschlussregeln müssen benannt werden. Die erste Lösung ist örtlich einfacher.

Eine widersprüchliche Formel **zu untersuchen** ist von ihrer **Annahme als wahr** zu unterscheiden. Werden `P` und `¬P` beide als Voraussetzungen akzeptiert, folgt klassisch jede Aussage `Q`: Aus `P` folgt `P∨Q`; zusammen mit `¬P` folgt daraus `Q`. Das begründet die Vorsicht bei Voraussetzungen. Es macht die Formel `P∧¬P` nicht zu einer beschädigten Formel und beweist keine Widersprüchlichkeit der Logik.

## 5. Selbstbezug, Barbier, Verbotstafel und Zirkelschluss einzeln geprüft

### Die eigene Metasymboldefinition

[Symbolteil 1417–1428](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:1417) setzt „in sich widerspruchsfrei“ ausdrücklich mit dem Ausschluss direkten und indirekten Selbstverweises gleich. **Als eigene Zulässigkeitsregel ist der Ausschluss möglich; als allgemeine Gleichsetzung mit logischer Widerspruchsfreiheit ist er falsch.**

Für einen elementaren Vergleich reichen Wahrheitswertbedingungen: `p↔p` lässt beide Werte zu, `p↔¬p` keinen. Ebenso lassen gegenseitige Bedingungen `p↔q` und `q↔p` die Belegungen `(wahr,wahr)` und `(nicht wahr,nicht wahr)` zu. Rückverweise allein entscheiden also weder Widerspruchsfreiheit noch eindeutige Bestimmtheit. Dies sind Gegenproben zur Gleichsetzung, keine Behauptung, damit sei bereits eine allgemeine Theorie selbstbezüglicher Sprache gegeben.

**Kleine Reparatur:** Die eigene Metasymbolregel als „Ausschluss von Verweiszyklen“ benennen und erklären, dass damit eine bestimmte Art von Bezeichnungsproblemen vermieden werden soll. Eine darüber hinausgehende Behauptung über alle Formen von Selbstbezug ist nicht nötig. Die frühere Rechts-links-Idee müsste anhand ihres vollständigen Wortlauts gesondert auf solche Zyklen geprüft werden; das gedruckte Lage-Beispiel enthält nicht schon allein wegen „vorher“ einen Verweiszyklus.

### Barbier: Unerfüllbare Existenzbedingung

**Fundstelle:** [Logikteil 1742–1839](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:1742).

Der Beweis funktioniert unter der Voraussetzung, dass der Barbier `b` selbst zur betrachteten Personengruppe `D` gehört und **genau alle** Personen dieser Gruppe rasiert, die sich nicht selbst rasieren. Mit `R(x,y)` für „x rasiert y“ lautet die Bedingung:

\[
b\in D,\qquad \forall x\in D:\ R(b,x)\leftrightarrow\neg R(x,x).
\]

Einsetzen von `x=b` ergibt `R(b,b)↔¬R(b,b)`. Das ist unter keiner klassischen Belegung wahr. **Folgerung: Ein solcher Barbier existiert unter diesen Bedingungen nicht.** Eine beschreibbare Bedingung garantiert ihre Erfüllung nicht. Läge der Barbier ausserhalb der betrachteten Gruppe, wäre dieses Einsetzen nicht gestattet.

Die vorgeschlagene Beschränkung auf andere Personen beseitigt das Problem: `∀x∈D: x≠b ⇒ (R(b,x)↔¬R(x,x))`. Sie macht über Selbst-Rasieren des Barbiers keine Vorgabe. Diese Fassung erhält auch das ursprüngliche „alle und nur diejenigen“; die kürzere sprachliche Ersatzfassung im Manuskript lässt diese Genauigkeit offen. Der Widerspruch ist eine Widerlegung der ursprünglichen Existenzannahme, kein Versagen der verwendeten Logik.

### Verbotstafel: Verbot und Tatsache sind unterschiedliche Inhalte

**Fundstelle:** [1857–1886](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:1857).

Aus „Es ist verboten, diese Tafel aufzustellen“ und „Diese Tafel wurde aufgestellt“ folgt kein Paar `P` und `¬P`: Ein Verbot behauptet nicht, dass die verbotene Handlung tatsächlich unterbleibt. Ein Aufstellen entgegen der aufgeschriebenen Regel ist als Beschreibung logisch möglich. Die Existenz der Tafel widerlegt also nicht schon den Inhalt eines Verbots. Auch folgt aus ihrem Nichtvorhandensein nicht ohne weitere Annahme, das Aufstellen sei erlaubt.

Die Ergänzung „andere Verbotstafeln“ kann die beabsichtigte Regel klarer machen. Sie repariert aber keinen zuvor nachgewiesenen aussagenlogischen Widerspruch. Fragen nach Geltung, Zeitpunkt und Ausnahmen der Regel müssten für eine genauere Modellierung zusätzlich festgelegt werden; sie werden hier nicht entschieden.

### Wind und Wolken: Eine zirkuläre Erklärung ist keine Kontradiktion

**Fundstelle:** [1890–1936](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:1890).

Das Erlebnis kann als Beispiel für eine unzureichende Erklärung stehen bleiben. Aber „P, weil Q“ und „Q, weil P“ zeigen allein weder `P∧¬P` noch die Falschheit von `P` oder `Q`. Selbst die beiden Implikationen `P⇒Q` und `Q⇒P` sind gemeinsam erfüllbar. Eine Begründung, die ihr Ergebnis bereits voraussetzt, liefert keinen unabhängigen Nachweis; daraus folgt keine innere Widersprüchlichkeit der Aussagen. Über die physikalische Ursache von Wind wird hier kein Befund behauptet.

### „Als nicht wahr kennzeichnen“ ist keine allgemeine Reparatur

**Fundstellen:** [1943–1991](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:1943); [Delta-Festlegung, Restposten 8542–8569](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:8542).

Für die gewöhnliche Kontradiktion `P∧¬P` ist der Wert „nicht wahr“ bereits durch die Wahrheitstafeln bestimmt. Man kann ihre Negation beweisen; ein zusätzlicher Warnzettel ist dafür nicht nötig. Bei widersprüchlichen Voraussetzungen muss dagegen geprüft werden, welche Voraussetzungen aufzugeben oder zu ändern sind. Eine zusätzliche Beschriftung beseitigt die alten Annahmen nicht.

Bei einer problematischen Wahrheits-Selbstreferenz darf man nicht einfach einen Wert setzen und sämtliche bisherigen Bedingungen beibehalten: Verlangt eine Interpretation `v(L)=1−v(L)`, erfüllt weder `v(L)=0` noch `v(L)=1` die Bedingung. Eine Zuordnung von 0 hilft nur, wenn die problematische Bedingung oder die Semantik mitgeändert wird. Diese Gegenprobe betrifft auch den pauschalen Zusatz in der Delta-Definition. Dort müssen gewöhnliche, stets nicht wahre Formeln und Ausdrücke ohne passende klassische Interpretation unterschieden werden.

## 6. Nicht gewusst, nicht bewiesen und nicht wahr

**Fundstellen:** [Negationskapitel 8402–8421](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:8402), [8471–8720](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:8471); [Vergleich mit Wahrscheinlichkeit 37105–37231](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:37105).

Der Wunsch, unbelegte Behauptungen nicht als gesicherte Wahrheiten auszugeben, ist sinnvoll. Die Folgerung [8409–8410](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:8409), man müsse bei fehlendem Wissen schreiben, die Aussage sei nicht wahr, ist jedoch falsch. Ebenso falsch ist die Behauptung, eine unzutreffende Negation könne keine falschen Schlüsse verursachen.

Gegenprobe: Sei `P` die wahre Aussage `1=1`. Wer aus mangelndem Wissen `¬P` als wahr übernimmt, übernimmt eine nicht wahre Voraussetzung. Aus ihr kann bereits durch die gültige Regel `¬P ⇒ (¬P∨Q)` die ebenfalls nicht wahre Aussage `¬P∨Q` folgen, wenn auch `Q` nicht wahr ist. Gültige Schlussregeln versprechen Wahrheitserhaltung **aus wahren Voraussetzungen**; sie machen unzutreffende Negationen nicht harmlos.

| Gemeinter Status | Sachgerechte Formulierung |
| --- | --- |
| Über den Wahrheitswert fehlt Wissen | „Ich weiss nicht, ob P.“ |
| Im gewählten System liegt kein Beweis vor | „P ist hier bislang nicht bewiesen.“ |
| Eine Aussage soll vorläufig untersucht werden | „Angenommen P …“; Folgen bleiben von dieser Annahme abhängig. |
| Die Aussage wird verneint | `¬P`; unter klassischer Interpretation wahr genau dann, wenn `P` nicht wahr ist. |

„Nicht wahr“ darf als eigener Name für den zweiten Wahrheitswert verwendet werden. Soll es dagegen, wie im Hunde-Pizza-Beispiel, „nicht als wahr bekannt“ bedeuten, passen die klassischen Negationstabellen und die späteren Gesetze nicht mehr unverändert dazu. Die kleinste Reparatur ist eine sprachliche Trennung von Wahrheitswert und Wissensstand; eine neue Logik ist dafür nicht nötig.

Auch eine Wahrscheinlichkeit zwischen 0 und 1 ist kein dritter Wahrheitswert eines konkreten Ereignisses. Das Aischa-Beispiel kann Unkenntnis oder Häufigkeiten erläutern; daraus folgt nicht, Zweiwertigkeit sei nur der Sonderfall einer Ereigniswahrscheinlichkeit von 0 oder 100 Prozent. Die physikalischen Behauptungen über Quantenmechanik werden damit ausdrücklich nicht mitgeprüft.

Ein weiterer örtlicher Fehler steht [bei 9625–9627](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:9625): „Ist die Aussage wahr, dann gilt nicht, dass die Negation der Aussage nicht wahr ist.“ Das zusätzliche „nicht“ kehrt die richtige Negationsregel um. Richtig: **Ist die Aussage wahr, dann ist ihre Negation nicht wahr.**

## 7. Was über Grenzen der Logik tatsächlich folgt

### „Es gibt wahre Aussagen“

**Fundstellen:** [1178–1429](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:1178); die Behauptung prinzipieller Unbeweisbarkeit [1492–1494](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:1492).

Eine Ausgangsannahme über Wahrheit kann als philosophische Setzung benannt werden. Die unbeschränkte Behauptung, die Existenz wahrer Aussagen könne weder bewiesen noch widerlegt werden, ist jedoch zu stark: In der vorausgesetzten klassischen Semantik ist `P∨¬P` unter jeder Belegung wahr. Damit gibt es in dieser Sprache wahre Formeln. Vor der Festlegung von Sprache, Semantik und Beweisregeln ist „beweisbar“ noch nicht hinreichend bestimmt.

Bei `∃A∈Ω: A` muss ausserdem geklärt werden, ob `A` über Formeln, Aussageinhalte oder Wahrheitswerte läuft. Quantifikation über Aussagen ist nicht schon Teil der gewöhnlichen Aussagenlogik; Quantifikation über Formelobjekte benötigt eine ausdrückliche Beziehung „ist unter v wahr“. Als metasprachliche Kurzschreibweise ist die Absicht verständlich. Die systematische Formelprüfung wird in Arbeitspaket 4 fortgesetzt.

### Gödel

**Fundstelle:** [1722–1726](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:1722).

Die Richtung der Bemerkung über Beweisgrenzen ist richtig, ihre Reichweite sollte präzisiert werden: Jede konsistente, effektiv axiomatisierbare Theorie, die genügend elementare Arithmetik umfasst, ist unvollständig; es gibt Sätze ihrer Sprache, die sie weder beweist noch widerlegt. Das ist eine Aussage über bestimmte formale Theorien. Es besagt weder, dass diese Theorien widersprüchlich sind, noch, dass das Lage-Beispiel eine solche Grenze nachweist. Siehe [Jeremy Avigad, Computability and Incompleteness, Satz 4.4.9 und Abschnitt 4.6](https://www.andrew.cmu.edu/user/avigad/Teaching/candi_notes.pdf), Buchseiten 104 und 110–112.

### Das „Zwischenhaltparadoxon“ ist im passenden Bereich beweisbar

**Fundstellen:** [Definition eines logischen Satzes 27178–27339](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:27178); [Vorbemerkung und offene Ersetzungsfrage 33726–33930](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:33726); [angekündigter Umweg über NAND 181752–181793](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:181752).

Der Text fragt, ob aus der Äquivalenz von `B` und `C` auch `A(B)↔A(C)` folgt. **Für endliche Formeln aus den festgelegten wahrheitsfunktionalen Verknüpfungen lautet die Antwort ja.** Der allgemeine Ersatz in beliebigen sprachlichen Umgebungen wäre dagegen nicht gerechtfertigt: Eine Aussage über die Buchstabenzahl einer zitierten Zeichenkette hängt von deren Schreibweise ab, nicht nur von deren Wahrheitswert.

Für die präzise Fassung bezeichne `F[p]` eine endliche Formel mit einem Platzhalter `p`. Beim Einsetzen bleiben die übrigen Formelbestandteile und ihre Interpretation gleich. Für jede Belegung `v` gilt:

\[
v(B)=v(C)\quad\Longrightarrow\quad v(F[B])=v(F[C]).
\]

**Beweis anhand des Formelaufbaus:**

1. Besteht die Formel nur aus `p`, ist die Behauptung genau die Voraussetzung. Besteht sie aus einem anderen atomaren Zeichen, bleibt dieses beim Einsetzen unverändert.
2. Ist sie `¬G[p]`, stimmen nach der schon begründeten Behauptung für die Teilformel die Werte von `G[B]` und `G[C]` überein. Negation liefert für gleiche Eingaben gleiche Ausgaben.
3. Ist sie `G[p] ◦ H[p]`, wobei `◦` eine der festgelegten zweistelligen Wahrheitsverknüpfungen ist, stimmen nach den Behauptungen für die beiden Teilformeln die jeweiligen Eingangswerte überein. Die Wahrheitstafel liefert damit auch am äusseren Verknüpfungszeichen denselben Wert.

Damit gilt die Behauptung für jede so aufgebaute endliche Formel, auch bei mehreren Vorkommen des Platzhalters. Folglich ist `(B↔C)⇒(F[B]↔F[C])` für jedes solche `F` eine Tautologie. Insbesondere ergibt eine bei allen Belegungen geltende Äquivalenz von `B` und `C` eine ebensolche Äquivalenz von `F[B]` und `F[C]`.

Hier wird ausdrücklich strukturelle Induktion über den endlichen Formelaufbau in der Metatheorie verwendet. Das ist eine benannte Beweisgrundlage, keine Herleitung jedes benötigten Aufbauprinzips aus voraussetzungsloser Logik. Der Umweg über NAND ist möglich, aber für diesen Beweis nicht erforderlich. Der Standard-Ersetzungssatz ist auch in [forall x: Calgary, Abschnitt 47.1](https://forallx.openlogicproject.org/html/Ch47.html) erläutert; der ausgeschriebene Aufbau-Beweis oben konkretisiert ihn für die hiesige Fragestellung.

Die bei [27291–27333](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:27291) vermutete innere Widersprüchlichkeit der Definition eines logischen Satzes ist ebenfalls nicht nachgewiesen. Dass `A(A₁,…,Aₙ)` einmal eine zusammengesetzte Formel bezeichnet und einmal behauptet wird, diese Formel sei wahr, ist eine Mehrdeutigkeit der Darstellung. Man kann sie durch „Für jede Belegung v gilt v(F)=1“ auflösen. Das unterscheidet den Bau einer Formel von ihrer Gültigkeit, ohne einen Widerspruch vorauszusetzen.

## 8. Das Mantra erhalten und präzisieren

Ein pauschales Streichen der wiederholten Voraussetzungen wäre dem Anliegen des Textes nicht angemessen. Sinnvoll sind eine anfängliche Erklärung und zwei je nach Zweck unterscheidbare Erinnerungen:

> „Es seien A und B Symbole für Aussagen. Ihr Inhalt und ihre Interpretation seien während der folgenden Umformung festgehalten; die Verknüpfungen werden nach den vereinbarten Wahrheitstafeln ausgewertet.“

Für ein tatsächlich als wahr vorausgesetztes System kommt gesondert hinzu:

> „Welche Aussagen wir als Voraussetzungen annehmen, halten wir ausdrücklich fest. Sie sollen unter der beabsichtigten Interpretation gemeinsam wahr sein.“

Die erste Erinnerung sichert die Anwendung der Wahrheitsfunktionen; die zweite betrifft die inhaltlichen Voraussetzungen eines Beweises. Aus dem blossen Wunsch nach Widerspruchsfreiheit ist ihre Erfüllung noch nicht bewiesen. Insbesondere werden mit der ersten Formulierung keine nicht wahren oder unerfüllbaren Formeln aus der Untersuchung ausgeschlossen.

## 9. Kleinstes zusammenhängendes Reparaturpaket

1. Bei der Aussagendefinition den weiten Symbolkettenbegriff und den engeren Bereich der Zweiwertlogik unterscheiden; die Zahl der geschriebenen Zeichen nicht mit Wahrheitsfähigkeit verknüpfen.
2. Die eigene Regel gegen Verweiszyklen als solche benennen. Selbstbezug, Unerfüllbarkeit, zirkuläre Begründung und kontextabhängiger Bezug erhalten getrennte Erklärungen.
3. Beim Lage-Beispiel den Bezug von „vorher“ festlegen und den Schluss auf innere Widersprüchlichkeit durch die Erklärung des Kontextwechsels ersetzen. Das Beispiel selbst und die wiederholten Erinnerungen bleiben erhalten.
4. Ω und den Untersuchungsbereich der Formeln klären; nicht wahre Formeln zulassen und gemeinsam angenommene Voraussetzungen davon unterscheiden. Die Delta-Zusatzregel entsprechend begrenzen.
5. Im Negationskapitel Nichtwissen und Verneinung trennen, die angebliche Harmlosigkeit falscher Negationen berichtigen und die zusätzliche Verneinung bei 9626 entfernen. In der Wahrscheinlichkeitsdiskussion nur die logische Verwechslung von Wahrheitswert und Unkenntnis örtlich korrigieren.
6. Beim Barbier die Personengruppe und die Existenzannahme nennen; Verbotstafel und Wolkenerlebnis als andere Arten von Problemen einordnen. Das blosse Kennzeichnen als nicht wahr nicht als allgemeine Reparatur ausgeben.
7. Die Gödel-Bemerkung auf den passenden Geltungsbereich beschränken. Für die Ersetzungsfrage Formelaufbau und Wahrheit unterscheiden und den oben angegebenen Beweis mit seiner Grundlage ergänzen.

Arbeitspaket 3 ist damit als dokumentierte fachliche Prüfung abgeschlossen. Die Ergebnisse vertiefen B1–B2 der [ersten Befunde](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/02_Erste_Befunde.md) und ergänzen sie insbesondere um die Ω-Problematik, die Verwechslung von Nichtwissen und Negation und den Beweis zur offenen Ersetzungsfrage. Die Übernahme einzelner Vorschläge ins Manuskript ist ein eigener Schritt. Als nächste nummerierte Aufgabe folgt Arbeitspaket 4 zur Mengenlehre und zu den Quantoren.
