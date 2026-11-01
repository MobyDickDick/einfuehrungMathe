# Prüfung der Begründungskette der natürlichen Zahlen

Stand: 1. November 2026. Ergebnis von Arbeitspaket 2 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Geprüft wurde die aktuelle eingebundene LyX-Quelle, einschliesslich der bereits vorhandenen lokalen Änderungen. Manuskript, PDF, Sicherungen und Autosavedateien wurden nicht verändert. Zeilenangaben bezeichnen LyX-Quellzeilen dieser Fassung, keine Buchseiten.

## Ergebnis und Reichweite

**Die Konstruktion mit nichtleeren endlichen Ketten eines festen Grundsymbols ist tragfähig. Die vorliegende Begründung ist aber noch nicht geschlossen.** Es fehlen vor allem eine ausdrücklich benannte Grundlage für endliche Ketten und ein Lemma über deren endlich viele Anfangsstücke. Mehrere weitere Lücken und falsche Formeln lassen sich örtlich beheben. Ein neues Axiom allein über die Vergleichbarkeit würde die entscheidende Lücke beim Minimumsatz nicht schliessen.

Der anschliessende Induktionsbeweis benutzt den Minimumsatz und das Vorgängerlemma. Nach Ergänzung seiner ausgelassenen Schritte funktioniert dieser Weg. Er gewinnt die Induktion damit aus Eigenschaften der gewählten Kettenstruktur; die stärkere Behauptung einer Herleitung allein aus elementarer Logik ist nicht gerechtfertigt.

Die folgende Prüfung unterscheidet **Definition**, **Voraussetzung**, **Beweis**, **Begründungslücke** und **falsche Formel**. Ungewöhnliche Begriffe, der Beginn der natürlichen Zahlen bei 1 sowie die persönliche Stimme sind keine Fehler. Untersucht wurden die tragenden Schritte bis zu Peano und die unmittelbar benötigten Ordnungs- und Minimumsätze. Die eingeschobene Zuordnung zu Mengen von Anfangsstücken ab Zeile 13120 und die spätere Arithmetik sind keine zusätzlichen Grundlagen dieser Beweiskette; ihre vollständige Einzelprüfung gehört nicht zu diesem Arbeitspaket. Die verwendeten Sätze der allgemeinen Logik und Mengenlehre werden hier als Voraussetzungen geführt, nicht sämtlich neu geprüft.

## 1. Welche Grundlage wird tatsächlich gebraucht?

Bereits [im Symbolteil vor der Gleichheitsdefinition](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:6377) werden zusammengesetzte Symbole auf endlich viele Bestandteile beschränkt. Die [Gleichheitsdefinition](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:6445) vergleicht zunächst Einzelzeichen und dann Anfangszeichen und Restketten. Sie führt die Gleichheit zusammengesetzter Zeichen auf die Gleichheit ihrer Bestandteile zurück. **Die Gleichheit der Grundzeichen selbst wird dabei vorausgesetzt.** Der Text sagt dies [bei Zeile 6647](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:6647) ausdrücklich.

Für die weitere Argumentation muss diese Grundgleichheit fest und eine Äquivalenzrelation sein. Die praktische Fähigkeit, beliebige Schriftzeichen zu unterscheiden, folgt nicht allein aus dem Satz vom ausgeschlossenen Dritten. Für die Zahlenkonstruktion reicht ein einziges festgelegtes Grundsymbol; schwierige Schrifterkennung muss deshalb nicht das Fundament belasten.

Folgende Voraussetzungen werden bisher teils stillschweigend gebraucht:

1. Ein festes, nichtleeres Grundsymbol `A` und eine festgehaltene Zerlegung in Grundsymbole. Ein Wort wie „Kuh“ kann dabei als vereinbarter ganzer Block dienen. Leerzeichen und Klammern zur Beschreibung der Ketten müssen von gezählten Bestandteilen unterscheidbar sein.
2. Nichtleere endliche Ketten aus `A`, deren Gleichheit sich nach der Folge ihrer Grundsymbole richtet. Verschiedene Namen für dieselbe Kette erzeugen keine verschiedenen Kettenobjekte.
3. Anhängen eines Grundsymbols und Verketten zweier endlicher Ketten liefern wieder endliche Ketten. Jede Kette ausser `A` entsteht durch Anhängen an eine kürzere nichtleere Kette. Fortgesetztes Entfernen des letzten Grundsymbols endet bei `A`.
4. Aussagen über alle solchen Ketten dürfen anhand ihres endlichen Aufbaus begründet werden. Wird dies formal als strukturelle Induktion formuliert, ist das ein Prinzip der zugrunde gelegten Theorie endlicher Ketten. Wird es als anschauliche Grunderfahrung verwendet, muss genau diese Rolle genannt werden.
5. Für Minimum- und Induktionsbeweise werden Mengen von Ketten beziehungsweise Zahlen und Teilmengen nach einer Eigenschaft gebildet; im Widerspruchsbeweis wird klassisch geschlossen.

Punkt 4 ist der entscheidende Ort der Grundlagenentscheidung. Er darf nicht unbemerkt als schon bewiesene Zahleninduktion benutzt und anschliessend als Herleitung derselben allein aus Logik ausgegeben werden. In einer ausdrücklich vorausgesetzten Theorie endlicher Wörter ist der Weg dagegen sinnvoll. Ein formales Vergleichsbeispiel bietet die [offizielle Darstellung induktiver Typen in Lean, Abschnitte 7.4–7.5](https://lean-lang.org/theorem_proving_in_lean4/Inductive-Types/): Dort gehören Aufbau- und Induktionsregeln zur Grundlage der Zahlen beziehungsweise Listen. Das ist eine Einordnung, keine Formalisierung dieses Manuskripts.

## 2. Abhängigkeiten im aktuellen Text

In der Tabelle bedeutet **bedingt tragfähig**, dass die jeweilige Behauptung mit der oben genannten Kettengrundlage funktioniert; es bescheinigt nicht die Fehlerfreiheit jeder ausgeschriebenen Formel.

| Schritt und Fundstelle | Was wird festgelegt oder behauptet? | Tatsächlich benötigt; Ergebnis |
| --- | --- | --- |
| [Symbolgleichheit, Symbolteil 6445](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:6445) | Rekursive Definition der Gleichheit zusammengesetzter Symbole | Grundgleichheit, eindeutige Zerlegung, endlicher Aufbau; eine Definition ersetzt diese Voraussetzungen nicht. |
| [Gleichheit entscheidbar, Zahlenteil 375](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:375); [Äquivalenzrelation, 562](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:562) | Vergleich endet; Gleichheit ist reflexiv, symmetrisch, transitiv | Das wiederholte Vergleichen der Reste setzt endlichen Abbau voraus. Entscheidbarkeit setzt zusätzlich entscheidbare Grundgleichheit voraus. Bedingt tragfähig. |
| [Einsetzen gleicher Teile, 946](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:946); [Assoziativität, 1210](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:1210) | Gleiche Ketten bleiben beim Verketten gleich; Gruppierung ändert die Kette nicht | Gleichheit, festgelegte Verkettung und Behandlung der Klammern als Beschreibung. Bedingt tragfähig. Einsetzen ist noch kein Kürzen. |
| [Echtes Verlängern, 1413](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:1413) | `AB ≠ A` | `B` muss nichtleer sein; endlicher Abbau verhindert Gleichheit mit einer echten Verlängerung. Der wiederholte Restvergleich gehört ausdrücklich in die Begründung. |
| [Ein Grundsymbol verschieben, 1983](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:1983); [Ketten kommutieren, 2525](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:2525) | `AB = BA` und `BC = CB`, wenn alle Bestandteile `A` sind | Im Text wird die Invarianz beim Umstellen gleicher Bestandteile anschaulich vorausgesetzt. Als Erfahrung benennbar; als formaler Beweis noch zu begründen. Die Aussage gilt nicht für beliebige Wörter über verschiedenen Grundsymbolen. |
| [Ordnung, 2848](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:2848) | `B < C` bedeutet `BD = C` für einen nichtleeren Rest; `≤` schliesst Gleichheit ein | Definition. Die Restketten müssen ausdrücklich aus demselben Grundsymbol bestehen. Existenz eines Restes für beliebige ungleiche Ketten wird noch nicht bewiesen. |
| [Trichotomie, 3412](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:3412) | Genau eine der Möglichkeiten `<`, `=`, `>` | Endlicher paarweiser Abbau und Ausschluss echter Selbstverlängerung. Ergänzung des Beweises nötig; siehe Abschnitt 3. |
| [Transitivität `<`, 5717](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:5717); [`≤`, 6358](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:6358); [Antisymmetrie, 6850](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:6850) | Ordnungseigenschaften | Für `<`: Reste verketten, `BE=C` und `CF=D` ergeben `B(EF)=D`. Für `≤`: Fallunterscheidung. Antisymmetrie braucht den Ausschluss gleichzeitiger strenger Gegenrichtungen. Bedingt tragfähig. Trichotomie allein ist noch nicht die ganze totale Ordnung. |
| [Minimumdefinitionen, 7152](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:7152), [7994](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:7994); [zwei Ketten, 7324](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:7324) | Minimum gehört zur Menge und liegt unter allen ihren Elementen | Definition; Existenz bei zwei Elementen folgt aus Vergleichbarkeit, Eindeutigkeit aus Antisymmetrie. Die formalen Definitionen enthalten Fehler; siehe Abschnitt 7. |
| [Endliche nichtleere Mengen, 8139](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:8139) | Minimum und Maximum existieren | Totalordnung und ein endliches Auswahl-/Vergleichsverfahren. Dessen Terminierung benutzt Endlichkeit der Menge, nicht bloss Endlichkeit jedes ihrer Elemente. Bedingt tragfähig. |
| [Minimum beliebiger nichtleerer Kettenmengen, 9791](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:9791) | Wohlordnung | Benötigt zusätzlich: Unter einer festen endlichen Kette liegen nur endlich viele verschiedene Ketten. Genau dies wird im vorhandenen Beweis nicht ausreichend begründet; siehe Abschnitt 4. |
| [Eigene Zahlendefinition, 10363](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10363); [Übertragung der Ordnung, 11736](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:11736) | Zahlen bezeichnen die Ketten; Gleichheit und Ordnung werden übertragen | Eindeutige Zuordnung von Zahlen zu Ketten, Abschluss unter Anhängen, keine weiteren Objekte. Die Definition über absteigende Zahlenfolgen setzt bereits Zahlen, Folgen und Ordnung voraus; siehe Abschnitt 5. |
| [Zweiter Minimumsatz, 12912](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:12912) | Jede nichtleere Zahlenteilmenge hat ein Minimum | Beruft sich auf das schon in die Zahlendefinition aufgenommene Verbot unendlicher Abstiegsketten. Er ersetzt die fehlende Grundlage nicht. Einfacher: reparierten Kettenminimumsatz übertragen. |
| [Peano 1–4, ab 14458](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:14458); [Vorgänger, 15008](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15008) | Anfangselement, Nachfolgerabschluss, 1 kein Nachfolger, Injektivität, Vorgänger für jede Zahl ausser 1 | Endlicher nichtleerer Kettenaufbau, echtes Verlängern, Kürzen gleicher Endzeichen und Vollständigkeit der Benennung aller Ketten. Diese Schritte brauchen den Minimumsatz nicht. Formel- und Begründungskorrekturen siehe Abschnitte 6–7. |
| [Induktion, 15227](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15227) | Anfang und allgemeiner Nachfolgerschritt tragen alle Zahlen | Minimumsatz, Vorgängerlemma mit kleinerem Vorgänger, Anfangsvoraussetzung und allgemeiner Schritt, Bildung der Gegenbeispielmenge, klassische Logik. Nach örtlicher Ergänzung tragfähig. |

Die Abhängigkeiten lassen sich damit so ordnen:

```text
festes Grundsymbol + Theorie nichtleerer endlicher Ketten
  ├─ Gleichheit, Verkettung, Kürzen, echtes Verlängern
  │    ├─ Vergleichbarkeit und Ordnung
  │    │    └─ Minima nichtleerer endlicher Mengen
  │    └─ endlich viele Anfangsstücke einer festen Kette
  │         └─ zusammen: Minimum beliebiger nichtleerer Kettenmengen
  └─ Benennung sämtlicher Ketten durch Zahlen; Nachfolger = Anhängen
       ├─ Peano 1–4 und Vorgängerlemma
       └─ übertragener Minimumsatz + Vorgängerlemma → Induktion
```

Hier ist der endliche Kettenaufbau eine Grundlage, kein aus der späteren Induktion gewonnener Zwischensatz.

## 3. Vergleichbarkeit: Was fehlt im ausführlichen Beweis?

**Fundstelle:** `prop:totale-Ordnung-Symbolketten-gleicher-Symbole`, [3412–3686](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:3412).

Der Text beginnt mit `BC = CB` und entfernt aus der Gesamtkette Grundsymbole, bis `B` oder `C` entsteht. Dann wird behauptet, die andere Kette sei in allen entsprechenden Zwischenketten enthalten. Das anschauliche Bild passt zur beabsichtigten Ordnung. Dass kein relevanter Zwischenstand übersprungen wird und die andere Kette tatsächlich als Anfangsstück erhalten bleibt, ist aber gerade eine Eigenschaft des endlichen Kettenaufbaus. Sie folgt nicht schon aus dem Kommutativitätslemma.

Ausserdem bedeutet die ausgeschriebene Disjunktion `B<C ∨ B=C ∨ B>C` lediglich **mindestens eine** Möglichkeit. Für „genau eine“ ist der gegenseitige Ausschluss nachzutragen.

**Kleine Reparatur:** Das Abtragen unmittelbar an den zwei Ketten erklären. Man streicht gleichzeitig je ein Grundsymbol am Anfang beider Ketten, solange beide noch eines besitzen. Wegen ihres endlichen Aufbaus endet dies. Sind beide gleichzeitig aufgebraucht, waren sie gleich. Bleibt nur bei `C` ein nichtleerer Rest `D`, gilt `BD=C`, also `B<C`; im umgekehrten Fall gilt `B>C`. Die leere Restkette ist hier nur ein Hilfsmittel des Vergleichs, keine natürliche Zahl 0.

Ein solcher Vergleich hat genau einen der drei Endzustände. Zusätzlich lässt sich der algebraische Ausschluss angeben: `B=C` und `BD=C` würden `BD=B` ergeben, entgegen dem Lemma über echte Verlängerung. Aus `BD=C` und `CE=B` würde durch Einsetzen und Assoziativität `B(DE)=B` folgen, ebenfalls unmöglich. Dabei sind `D` und `E` nichtleer.

So benötigt der Vergleichsbeweis keine vorherige Kommutativität der Verkettung gleichartiger Ketten. Er benötigt weiterhin den ausdrücklich vorausgesetzten endlichen Abbau. Den Satz allein zum Axiom zu erklären, würde dagegen die weiter unten benötigte Wohlordnung offenlassen: Auch die ganzen Zahlen sind total geordnet, ohne dass jede nichtleere Teilmenge ein Minimum hat.

## 4. Minimumsatz: Die fehlende Brücke lässt sich genau benennen

**Fundstelle:** `lem:Minimum-beliebiger-Teilmenge-natuerlicher-Zahlen`, [9791–10006](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:9791).

Der Ansatz ist gut: Wähle `B∈M` und setze

\[
D=\{C\in M\mid C\le B\},\qquad
E=\{C\in M\mid C\ge B\}.
\]

Beide Mengen enthalten `B`; aus der Vergleichbarkeit folgt `M=D∪E`, und `min E=B`. Die gesamte Last liegt nun darauf, dass `D` endlich ist.

Der vorhandene Widerspruchsversuch [ab Zeile 9929](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:9929) wechselt zwischen `D`, `B` und `C` als Mengen und Elementen. Auch nach blossen Buchstabenkorrekturen gilt nicht allgemein: Eine unendliche total geordnete Menge habe zu jedem Element ein grösseres. Beispielsweise ist `{1, 1/2, 1/3, …}` unendlich und hat trotzdem ein grösstes Element. Die Besonderheit der endlichen gleichartigen Ketten muss benutzt werden.

**Einzufügendes Lemma:** Zu jeder nichtleeren endlichen Kette `B` aus `A` gibt es nur endlich viele verschiedene nichtleere Anfangsstücke. Jede Kette `C≤B` ist ein solches Anfangsstück: entweder `C=B`, oder `B=CR` mit einem nichtleeren Rest `R`.

Die Endlichkeit der Anfangsstücke folgt aus dem endlichen Aufbau: `A` hat nur sich selbst als nichtleeres Anfangsstück. Beim Anhängen eines weiteren `A` bleiben die bisherigen Anfangsstücke erhalten und es kommt genau die ganze neue Kette hinzu. Das ist eine Begründung anhand des Aufbaus der Ketten, also gegebenenfalls strukturelle Induktion in der vorausgesetzten Kettentheorie. Die blosse Umbenennung in „Abtragen“ beseitigt diese Grundlage nicht.

**Reparierter Beweisschluss:** `D` ist eine Teilmenge der endlich vielen Anfangsstücke von `B` und enthält `B`. Daher besitzt `D` nach dem endlichen Minimumlemma ein Minimum `G`. Für jedes `C∈M` gilt:

- Liegt `C` in `D`, so ist `G≤C`.
- Liegt `C` in `E`, so ist `B≤C`. Wegen `B∈D` gilt auch `G≤B`; Transitivität liefert `G≤C`.

Da `G∈D⊆M`, ist `G=min M`. Die Eindeutigkeit folgt aus Antisymmetrie. Es muss kein Minimum einer unendlichen Menge vorausgesetzt werden, um den Beweis zu führen.

Damit entfällt auch die unklare Schlussformel `min M=min{G,C}` [bei Zeile 9989](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:9989). Ein fest gewähltes `C` ist dort nicht eingeführt. Sollte `B` gemeint sein, ist die Formel nach `G≤B` zwar richtig, aber der direkte Schluss `min M=G` reicht.

Hier wird keine gleichmässige Schranke für die Längen aller Ketten in `M` vorausgesetzt. Eine einzige ausgewählte Kette `B∈M` begrenzt die für das Minimum relevante Teilmenge `D`. Das ist der entscheidende Unterschied zwischen Endlichkeit jedes einzelnen Elements und Endlichkeit der ganzen Menge.

## 5. Zahlendefinition und zweiter Minimumsatz

**Fundstellen:** [10363–10573](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10363), Erläuterung [10750](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10750), zweiter Minimumsatz [12912–13078](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:12912).

`1·A=A` und `(n+1)·A=n·A A` benennen den Anfang und das Anhängen. Der Satz „Weitere Elemente … seien nicht vorhanden“ muss präzise bedeuten: **Alle Zahlen bezeichnen genau die auf diese Weise endlich aufgebauten Ketten.** Für jede solche Kette gibt es eine Zahl; verschiedene Zahlenschreibweisen mit derselben Kette gelten als gleich. Wird zwischen verschiedenen Grundsymbolen gewechselt, muss die entsprechende blockweise Ersetzung die Gleichheit und den Nachfolger erhalten. Am einfachsten wird zunächst mit einem festen `A` konstruiert und der Wechsel des Grundsymbols anschliessend erläutert.

Das zusätzliche Verbot einer unendlichen streng absteigenden Folge wird dagegen schon mit `ℕ`, Zahlenfolgen und der Zahlenordnung formuliert. Es kann als Folgerung oder Erläuterung zu einer vorausgesetzten Kettengrundlage dienen. Als erstmalige Definition von „endlich“ innerhalb derselben Zahlendefinition legt es seine eigenen Hilfsmittel noch nicht unabhängig fest.

Beim zweiten Minimumbeweis wird dieses Verbot ausdrücklich eingesetzt: Hätte `M` kein Minimum, könnte zu jedem Element ein kleineres ausgewählt und so eine unendliche absteigende Folge gebildet werden. Neben der schon vorhandenen Ordnung braucht dieser Schritt eine Begründung der fortgesetzten Auswahl und Folgenbildung. In einer üblichen hinreichend starken Mengenlehre lässt sich damit arbeiten; aus den bisherigen elementaren Logikregeln allein folgt die Konstruktion noch nicht. Es ist kein zweiter unabhängiger Beweis der fehlenden Endlichkeitsgrundlage.

**Kleine Reparatur:** Den reparierten Kettenminimumsatz auf die Zahlen übertragen. Die absteigenden Folgen können danach als Folgerung besprochen werden. Der Übergang gelingt direkt: Die zu einer nichtleeren Zahlenteilmenge gehörenden Ketten haben eine kleinste Kette, deren Zahlenbezeichner wegen der übertragenen Ordnung die kleinste Zahl ist.

Warum „keine weiteren Elemente“ mehr ist als eine harmlose Nachbemerkung, zeigt ein Gegenmodell zu den ersten vier Nachfolgereigenschaften allein: Neben der positiven Zahlenkette wird eine getrennte, in beide Richtungen unbegrenzte Kette mit Positionen aus `ℤ` zugelassen. Auf beiden Komponenten geht der Nachfolger eine Position weiter; die ausgezeichnete `1` liegt in der ersten Komponente. Der Nachfolger ist überall definiert und injektiv, und `1` ist kein Nachfolger. Auch jedes andere Element hat einen Vorgänger. Trotzdem scheitert Induktion für die Eigenschaft „liegt in der Komponente von 1“. Endliches Erzeugtsein beziehungsweise der Ausschluss solcher zusätzlichen Komponenten muss also wirklich begründet oder vorausgesetzt werden.

## 6. Vorgänger, Induktion und die Peano-Eigenschaften

### Vorgänger und Kürzen

**Fundstelle:** `lem:Vorgaenger-natuerliche-Zahl`, [15008–15220](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15008).

Der Text folgert aus `n≠1`, dass die zugehörige Kette mehr als ein Grundsymbol besitzt, und entfernt ein Zeichen. Der nichtleere Rest muss wiederum eine zulässige endliche Kette sein und deshalb einen Zahlenbezeichner `m` besitzen. Genau hier wird die Vollständigkeit der Benennung aller Ketten gebraucht. Dann folgt unmittelbar `n·A=m·A A`, also `n=m+1`. Weil ein Zeichen angehängt wurde, gilt auch `m<n`. Diese Ungleichung sollte im Lemma ausdrücklich mitgeführt werden; sie wird im Induktionsbeweis gebraucht.

Die vorherige Umstellung `n·A A=A n·A` ist dafür nicht nötig. Eine eigene Kürzungsregel macht ausserdem die Injektivität des Nachfolgers durchsichtig:

\[
UA=VA\ \Longrightarrow\ U=V.
\]

Denn nach Entfernen des gleichen letzten Grundsymbols müssen die verbleibenden Folgen positionsweise gleich sein. Hier werden **gleiche Teile aus gleichen Ketten entfernt**. Das ist die Umkehrung der früher bewiesenen Erhaltung von Gleichheit beim Anhängen und sollte gesondert aus der Kettengleichheit begründet werden.

### Induktion mit möglichst wenig Änderung am bestehenden Beweis

**Fundstelle:** `prop:vollstaendige-Induktion`, [15227–15455](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15227).

Die zu beweisende Aussage sollte ausdrücklich lauten: Für eine festgehaltene Eigenschaft `P` gilt

\[
\left(P(1)\land
\forall n\in\mathbb N\,[P(n)\Rightarrow P(n+1)]\right)
\Rightarrow\forall n\in\mathbb N\,P(n).
\]

Die beiden Voraussetzungen stehen im sprachlichen Beweis bereits. Der Text wählt dann die verschobene Gegenbeispielmenge `W={n∈ℕ | ¬P(n+1)}`. Auch diese Wahl funktioniert; sie erfordert die folgenden Ergänzungen:

1. Angenommen, `¬P(m)` für eine natürliche Zahl `m`. Wegen `P(1)` ist `m≠1`. Das Vorgängerlemma liefert `m=v+1` mit `v∈ℕ`; also ist `v∈W`. Damit ist `W` nachweislich nichtleer.
2. Nach dem reparierten und auf Zahlen übertragenen Minimumsatz gibt es `w=min W`. Folglich gilt `¬P(w+1)`.
3. Ist `w=1`, so gilt `P(w)` nach der Anfangsvoraussetzung. Ist `w≠1`, gibt es nach dem Vorgängerlemma ein `u∈ℕ` mit `w=u+1` und `u<w`. Wegen der Minimalität von `w` gehört `u` nicht zu `W`. Also gilt `¬¬P(u+1)` und klassisch `P(w)`.
4. Der allgemeine Induktionsschritt, auf `w` angewendet, ergibt `P(w+1)`, im Widerspruch zu Schritt 2. Daher gibt es kein Gegenbeispiel `m`, und alle `P(n)` sind wahr.

Das schliesst genau die beiden in B5 der ersten Befunde markierten Lücken. Überall ist derselbe Index `w` zu verwenden; `A_W` und das nicht eingeführte `p` haben an dieser Stelle keine eigene Rolle.

Alternativ kann die Menge der Gegenbeispiele ohne Verschiebung gewählt werden: `F={n∈ℕ | ¬P(n)}`. Ihr Minimum ist ungleich 1, sein kleinerer Vorgänger erfüllt `P`, und der Schritt liefert den Widerspruch. Das ist etwas kürzer; die bestehende Wahl von `W` muss dafür aber nicht aufgegeben werden. Die [Southampton-Vorlesungsnotizen, Proposition 10.1](https://www.southampton.ac.uk/~wright/1001/appendix-a---well-ordering-principle.html) zeigen den üblichen Zusammenhang zwischen Minimumprinzip und Induktion für positive ganze Zahlen. Der konkrete Abgleich mit den ausgelassenen Schritten oben beruht auf der hiesigen Quelle.

### Was damit über Peano gezeigt wird

Nach den genannten Reparaturen gilt in der konstruierten Struktur:

| Peano-Eigenschaft bei Beginn mit 1 | Begründung in der Kettenstruktur |
| --- | --- |
| `1∈ℕ` | `1` bezeichnet die Kette `A`. |
| `n∈ℕ ⇒ n+1∈ℕ` | Anhängen erhält den endlichen Kettenaufbau. |
| `n+1≠1` | Eine nichtleere Kette mit angehängtem Grundsymbol ist keine Einzeichenkette. |
| `m+1=n+1 ⇒ m=n` | Gleiches Endzeichen kürzen. |
| Induktionsprinzip | Reparierter Minimumsatz, kleinerer Vorgänger und obiger Widerspruchsbeweis. |

Die ersten vier Eigenschaften sind damit von der späteren Induktion unabhängig begründbar. Die fünfte benötigt den wesentlichen Vollständigkeits-/Endlichkeitsgehalt der Kettengrundlage. Ob Induktion für jedes zulässige Prädikat als Schema oder für sämtliche Teilmengen formuliert wird, hängt von der gewählten formalen Grundlage ab; der vorliegende naive Aufbau entscheidet diese Frage noch nicht.

**Örtlicher Ersatz für den zu starken Anspruch:** „Aus den vorausgesetzten Eigenschaften endlicher Symbolketten können wir für die so definierten natürlichen Zahlen die Peano-Eigenschaften einschliesslich des Induktionsprinzips herleiten.“ Dies ist ein fachlicher Formulierungsvorschlag, keine bereits vorgenommene Manuskriptänderung. Die Kapitelüberschrift [bei 14302](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:14302) kann als zugespitzte Frage stehen bleiben, sofern die Antwort deutlich macht: Als Sätze innerhalb einer anderen Grundlage verlieren Peanos Eigenschaften nicht ihren Status als Axiome einer Peano-Axiomatisierung.

Die Nachbemerkung [bei 15462–15490](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15462) braucht zwei fachliche Korrekturen: Induktion wird durchaus aus anderen Grundlagen bewiesen; und vollständige mathematische Induktion ist eine deduktive Beweismethode. Sie ist kein unsicherer allgemeiner Schluss aus einer Sammlung bestätigender Einzelfälle.

## 7. Konkrete lokale Fehler entlang dieser Kette

Diese Liste ergänzt die grundlegenden Lücken. Sie ist keine vollständige Formelprüfung des gesamten Zahlenteils. Bei sprachlichen Erläuterungen ist jeweils die fachliche Richtung gemeint, keine stilistische Glättung.

| Fundstelle | Befund und kleinste Reparatur |
| --- | --- |
| [3433](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:3433), [3731](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:3731), [5730](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:5730), [5890](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:5890) | Die Ketten sollen aus `A` bestehen, nicht aus `C`. Bei 5730 sind die Ketten `B,C,D` gemeint. Das betrifft die mathematischen Voraussetzungen der Sätze. |
| [3791](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:3791), [3830](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:3830) | In `B=C ⇒ C ∨ B=C` steht die Kette `C` an einer Aussagenstelle. Etwa `B=C ⇒ (B=C ∨ B=C)` ist als Verdopplung richtig. Die spätere Implikation von `B<C ∨ B=C ∨ B>C` zu `B<C ∨ B=C ∨ B=C ∨ B=C` ist falsch, wenn `B>C`. Für den ganzen Korollarbeweis reichen die drei Fälle `<`, `=`, `>` und die Definitionen von `≤` und `≥`. |
| [5916](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:5916) | `B≤C ⇔ C≥C` ist falsch, etwa für `B=AA`, `C=A`. Rechts muss `C≥B` stehen. Der nachfolgende Beweis verwendet bereits diese richtige Form. |
| [7183](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:7183) | Beim Zweierminimum muss `E` allquantifiziert sein: `D∈{B,C} ∧ ∀E∈{B,C}: D≤E`; entsprechend `D≥E` für das Maximum. |
| [7232–7268](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:7232) | Die zweite sprachliche Erläuterung meint das **Maximum** und muss `D≥B` sowie `D≥C` verlangen. |
| [7533–7564](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:7533) | Im Fall `B<C` wird plötzlich `B>C` als Voraussetzung verwendet. Für `max{B,C}=C` ist aus `B<C` vielmehr `C>B` und dann `C≥B` zu folgern. |
| [7899](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:7899), [7961–7970](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:7961) | Im Fall `B>C` muss für das Maximum `B∈{B,C}` verwendet werden. Am Ende müssen `B≥C` und `B=max{B,C}` stehen; `C≥B` und `C=max{B,C}` sind in diesem Fall falsch. |
| [8114–8128](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:8114) | **Erheblicher Definitionsfehler:** Die Zugehörigkeit von `C` steht innerhalb des Vordersatzes einer Implikation. Für `C∉M` wird diese automatisch wahr. Richtig: `C=min M ⇔ (C∈M ∧ ∀B∈M: C≤B)`; für das Maximum `C≥B`. Gegenprobe: `M={A}`, `C=AA` erfüllt die vorhandene Implikation für jedes `B`, ist aber kein Minimum. |
| [8175](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:8175), [9827](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:9827) | Endlichkeit und Nichtleerheit getrennt fordern. Als ausdrücklich lokale Konvention kann „endlich viel“ zwar nichtleer gemeint sein; daraus folgt aber nicht allgemein, endliche Mengen seien nichtleer. Im Minimumsatz für beliebige Mengen muss unabhängig von ihrer Grösse `M≠∅` stehen. |
| [8226–8227](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:8226) | Bei einer Einermenge steht zunächst `A=min{…} S` beziehungsweise `A=max{…} S`. Das angehängte `S` muss entfallen; die spätere Formel bei 8294 ist bereits richtig. |
| [8556](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:8556), [8649](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:8649) | Im zweiten endlichen Min/Max-Beweis wird aus `S=BC` oder `S=BCD` die falsche Formel `B<C` gefolgert. Gemeint ist jeweils `B<S`. Die Verwechslung des Grundsymbols `S` mit der Gesamtkette `S` sollte dabei durch einen anderen Namen für die Gesamtkette vermieden werden. |
| [12339–12391](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:12339) | Das dort verwendete Verteilungsgesetz muss `(U⇒(V∧W)) ⇔ ((U⇒V)∧(U⇒W))` lauten. Im Text steht rechts stattdessen `(U⇒V)∧(U∧W)`. Bei `U` falsch ist links wahr und rechts falsch. Die richtige Regel in den drei betreffenden Formeln einsetzen. |
| [12649](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:12649) | Im ersten Fall der Zahlentrichotomie folgt aus `n₁≤n₂` und `n₁≠n₂` gerade `n₁<n₂`; die dortige Folgerung `n₁=n₂` ist falsch. |
| [12828](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:12828) | In der Fallunterscheidung für `min{n₁,n₂}` muss die letzte Bedingung `n₁>n₂` statt nochmals `n₁=n₂` lauten. Sonst fehlt etwa für `n₁=2,n₂=1` jeder Fall. |
| [12940](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:12940) | `∀n∈M: m_M≤m` lässt `m` frei. Richtig ist `∀n∈M: m_M≤n`. |
| [14361](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:14361) | Die Induktionsformel bindet die Variablen nicht in der benötigten Weise. Durch die Formel aus Abschnitt 6 ersetzen; insbesondere gehört der **allgemeine** Nachfolgerschritt in die Voraussetzungen. |
| [14766–14805](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:14766) | Im dritten Peano-Beweis kehrt „Dann kann auch nicht … ≠ … gelten“ die richtige Aussage um. Aus `A≠A n·A` folgt durch Symmetrie der Gleichheit beziehungsweise Ungleichheit `A n·A≠A`, also `n+1≠1`. Die beiden verneinenden Wendungen vor den Ungleichungen müssen fachlich korrigiert werden. |
| [14841](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:14841) | Der vierte Peano-Satz behauptet `m+1=n+1 ⇒ n=1`. Falsch bereits für `m=n=2`. Richtig ist `m=n`. Der anschliessende Beweis erreicht diese richtige Aussage bereits. |
| [15342–15444](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15342) | Nichtleerheit von `W` und die Begründung von `P(w)` ergänzen; `A_W` zu `A_w` und `p` zu `w` berichtigen. Siehe Abschnitt 6. |

Einige Querverweise erzeugen ausserdem den falschen Eindruck zusätzlicher Abhängigkeiten: Die ersten beiden Peano-Beweise verweisen auf `prop:Minimum-Teilmenge-natuerlicher-Zahlen`, obwohl die **Zahlendefinition** gemeint ist. `lem:Peano-Rueckschritt` [bei 15526](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15526) nennt Kommutation, verweist aber auf die erst später bewiesene Assoziativität der Addition. Für `m+1=1+m` wäre das schon vorhandene `lem:Kommutation-n-1-natuerliche-Zahlen` passend; unmittelbares Rechtskürzen kommt ganz ohne diesen Verweis aus. Die falschen Gleichheitslabel `lem:Gleichheit-Symbole-Aequivalenzrelation` sollten auf das vorhandene `lem:Symbolgleichheit-ist-Aequivalenzrelation` zeigen. Die vollständige technische Querverweisprüfung bleibt Arbeitspaket 7.

## 8. Kleinstes zusammenhängendes Reparaturpaket

Die folgenden Änderungen würden die untersuchte Kette schliessen, wenn die Theorie endlicher Ketten ausdrücklich als Grundlage akzeptiert wird:

1. Vor den Kettenbeweisen die Voraussetzungen aus Abschnitt 1 benennen: festes Grundsymbol, Gleichheit, endlicher Aufbau und Abbau, Abschluss, keine zusätzlichen Kettenobjekte. Zahlenbenennung und Kettenobjekte unterscheiden.
2. Eine Kürzungsregel und das Lemma über endlich viele Anfangsstücke ausdrücklich begründen. Dabei offen sagen, welche Form des Schlusses anhand des endlichen Aufbaus vorausgesetzt wird.
3. Im Vergleichssatz den paarweisen Abbau und den gegenseitigen Ausschluss der drei Fälle nachtragen. Er muss dann nicht die ungeklärte allgemeine Umstellungsargumentation tragen.
4. Minimumdefinitionen berichtigen; den Minimumsatz über die endliche nichtleere Menge `D` wie in Abschnitt 4 abschliessen und auf Zahlen übertragen. Das Verbot absteigender Zahlenfolgen als Folgerung beziehungsweise Erläuterung nachordnen.
5. Im Vorgängerlemma den kleineren Vorgänger ausweisen; im Induktionsbeweis die zwei fehlenden Verbindungen und die einheitliche Indexschreibung ergänzen. Die lokalen falschen Formeln aus Abschnitt 7 korrigieren.
6. Den Geltungsanspruch bei Peano und Induktion an die tatsächlich verwendete Grundlage anpassen. Die Beweise über Anfang, Nachfolger und Injektivität brauchen dabei keinen Rückgriff auf den Minimumsatz.

Das ist ein konkreter Vorschlag für örtliche Reparaturen. Eine Übernahme ins Manuskript ist in diesem Arbeitspaket nicht erfolgt. Die fachliche Entscheidung lautet nicht, ob die Symbolkettenidee aufgegeben werden muss. Zu entscheiden ist, **wie ausdrücklich die ohnehin verwendete Vorstellung endlichen Aufbaus als Grundlage genannt wird**. Wer stattdessen aus einer schwächeren formalen Grundlage beginnen möchte, muss diese erst festlegen; mit einem zusätzlichen Vergleichbarkeitsaxiom allein wäre es nicht getan.

Arbeitspaket 2 ist damit als dokumentierte Prüfung abgeschlossen. In der nummerierten Liste folgt Arbeitspaket 3 zum Aussagenbegriff. Der für Arbeitspaket 8 vorgemerkte Wiedereinstieg kann nun auch auf einen kurzen Einschub zur Kettengrundlage aufbauen; ein ausformulierter Anschluss in Markus’ Stimme bleibt ein eigener Schritt.
