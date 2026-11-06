# Manuskriptaufbau und technische Altlasten

Stand: 6. November 2026. Ergebnis von Arbeitspaket 7 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Fundstellen bezeichnen Quellzeilen, keine Buchseiten. Manuskript, Exporte und Sicherungen wurden nicht verändert oder gelöscht.

## 1. Ergebnis und Massstab

**Die aktuelle Arbeitsfassung lässt sich eindeutig bestimmen. Ihre technischen Querverweise sind wesentlich aufgeräumter, als die vielen älteren Dateien zunächst vermuten lassen:** Alle 3’736 erfassten Verweisvorkommen besitzen ein Ziel, und alle 1’152 Zielnamen sind eindeutig. Auch die 70 eingebundenen Grafikvorkommen sind als Dateien vorhanden. Die verbleibenden Fragen betreffen vor allem die sachliche Wahl einzelner Verweisziele, ausdrücklich vorgemerkte Ergänzungen und die Zuordnung von Arbeitsmaterial.

Das Skript dient Markus’ eigener Auseinandersetzung mit Mathematik. Veröffentlichungsreife ist kein Ziel dieses Arbeitspakets. Der Zugang über Symbole, Metasymbole und das Sichtbarmachen kleiner Denkschritte ist die inhaltliche Leitidee, an der die Ordnung des Materials sich orientieren soll. Persönliche Stimme, Humor, ausführliche Beweise und Abschweifungen sind dadurch kein technischer Mangel. Die folgenden Befunde bewerten die Dateiorganisation und konkrete Verweisstellen, nicht den Wert des Vorhabens.

| Gegenstand | Ergebnis |
| --- | --- |
| Aktuelle Quellen | Hauptdatei mit sechs direkt eingebundenen Teilen; keine weiteren verschachtelten Einbindungen in diesen Teilen. |
| Doppeltes Peano-Folgekapitel | Zwei ausgegebene Vorkommen desselben Textes und derselben Formeln; Unterschiede bei fünf Zielnamen samt internen Verweisen sowie bei Absatzformatierung. Die Absicht der Wiederholung bleibt offen. |
| Technische Verweisauflösung | Kein fehlendes Ziel und kein doppelt vergebener Zielname im geprüften Verbund. |
| Sachliche Verweiszuordnung | Konkrete unpassende Ziele und vermeidbare Rückbezüge auf spätere Induktionsübungen sind unten mit örtlichen Vorschlägen erfasst. |
| Noch einzufügende Verweise | 29 entsprechende LyX-Notizen; vorhandene Anknüpfungspunkte und offene Ziele sind unterschieden. |
| Restposten | Eingebundenes Arbeitsmaterial mit bereits genutzten Definitionen und Beweisen; einzelne unfertige Ansätze stehen zwischen längeren ausgearbeiteten Abschnitten. |
| Exporte und Sicherungen | TeX-Dateien, Bestands-PDF, Autosaves, Versionssicherungen und ältere Sammelfassung haben unterschiedliche Stände und Funktionen. Keine davon wurde allein nach Datum oder Dateigrösse zur Hauptfassung erklärt. |

## 2. Welche Dateien zur aktuellen Fassung gehören

Massgeblich ist die tatsächlich vorhandene Einbindung in [EinfuehrungMathe.lyx ab 236](C:/Users/marku/myCloud/Mathe/EinfuehrungMathe.lyx:236), nicht die Zahl der ähnlich benannten Dateien im Ordner.

| Reihenfolge | Quelle | Einbindung in der Hauptdatei | Quellzeilen |
| --- | --- | --- | ---: |
| Rahmen, Titel, Anhang | `EinfuehrungMathe.lyx` | Hauptdatei | 1’711 |
| 1 | `Teil_Einleitung.lyx` | 238 | 3’499 |
| 2 | `Teil_Symbole.lyx` | 249 | 6’735 |
| 3 | `Teil_Logik.lyx` | 260 | 288’742 |
| 4 | `Teil_Mengenlehre.lyx` | 268 | 25’330 |
| 5 | `Teil_natuerliche_Zahlen.lyx` | 279 | 22’436 |
| 6 | `Restposten.lyx` | 290 | 30’284 |

Die Symboltabelle des Anhangs steht anschliessend **in der Hauptdatei**, [ab 298](C:/Users/marku/myCloud/Mathe/EinfuehrungMathe.lyx:298). Sie gehört nicht zusätzlich in die aktuelle Restpostendatei. Alle sieben aktiven LyX-Dateien verwenden Format 643. Die Kopfdefinitionen der Zweige „Frage“ und „Antwort“ sind vorhanden, aber in diesen Quellen gibt es keine entsprechenden Branch-Inhalte, die die beiden Peano-Kapitel unterschiedlich ein- oder ausblenden würden. Eingeklappte LyX-Ansichten sind ebenfalls keine Ausblendung im Export. Ausgeblendete Arbeitsnotizen sind gesonderte `Note Note`-Insets.

### Exporte, Sicherungen und andere Texte

| Datei oder Dateigruppe | Einordnung und nachprüfbarer Unterschied |
| --- | --- |
| `Teil_Logik.tex`, `Teil_Mengenlehre.tex`, `Teil_natuerliche_Zahlen.tex`, `Teil_Symbole.tex` | Vorhandene ältere TeX-Exporte vom 7. August 2026, keine zusätzlich eingebundenen Arbeitsquellen. Insbesondere enthält der Zahlenexport nur **ein** Peano-Folgekapitel, bei TeX-Zeile 4793. Er bildet die aktuelle LyX-Doppelung nicht ab. Der Zahlenexport ist mit der älteren Zeichenkodierung Windows-1252 lesbar; seine Umlaute dürfen nicht durch ungeprüftes Einlesen und Speichern als UTF-8 beschädigt werden. |
| `EinfuehrungMathe.pdf` | Bestandsausgabe mit 1’048 PDF-Seiten; Erstellungsdatum laut PDF-Metadaten: 6. September 2026. Sie ist damit nicht einfach mit den August-TeX-Dateien gleichzusetzen. Sie enthält beide Peano-Folgekapitel als Kapitel 36 und 37. Die spätere Selbstbemerkung zur Vergleichbarkeit bei Zahlen-Quellzeile 3689 fehlt im extrahierten, nach Leerraum vereinheitlichten PDF-Text. Die PDF ist folglich ebenfalls kein vollständiges Abbild der jetzigen Quelle. |
| `Teil_Logik_und_Mengenlehre.lyx` | Ältere, nicht eingebundene Sammelfassung in Format 620. Ihre 942 LyX-Labelnamen finden sich sämtlich in den beiden getrennten aktuellen Dateien wieder: 854 im Logikteil und 88 im Mengenteil. Das belegt die gemeinsame Herkunft, keine vollständige Textgleichheit. Nicht parallel einbinden: Dadurch würden dieselben Zielnamen erneut auftreten. |
| `*.lyx~` | Versionssicherungen, keine pauschal entbehrlichen Dubletten. `Teil_Symbole.lyx~` ist bytegleich zur aktuellen Symbolquelle; bei den anderen verglichenen Quellen gibt es Unterschiede. Die Zahlensicherung unterscheidet sich an einer Passage der Wardhaugh-Leseerinnerung; sie ist nicht einfach dieselbe Datei unter anderem Namen. |
| `Restposten.lyx~` | Enthält zusätzlich einen Einleitungsblock und am Ende den Anhang samt Symboltabelle. Der grosse Umfangsunterschied zur aktuellen Restpostendatei bedeutet deshalb nicht, dass dort einfach tausende Zeilen neuer Mathematik fehlen. Auch eine Grafikpfadzeile unterscheidet sich. Die Sicherung bleibt als eigener historischer Stand erhalten. |
| `Teil_Einleitung.lyx~` | Umfangreiche frühere Sammelfassung: neben der Einleitung enthält sie auch die Themen der Restposten und den anschliessenden Anhang. Ihre Grösse macht sie nicht zur aktuellen Einleitungsquelle. |
| `EinfuehrungMathe.lyx~` | Enthält gegenüber der Hauptdatei eine zusätzliche einfache `cancel`-Paketladung vor der Paketladung mit `makeroom`. Diese zusätzliche Zeile steht **nicht** in der aktuellen Hauptdatei. Ein blindes Zurückkopieren würde also auch technische Einstellungen zurückholen. |
| `#Teil_Logik.lyx#`, `#Teil_Mengenlehre.lyx#`, `#Teil_natuerliche_Zahlen.lyx#` | Autosave-Dateien; keine der drei ist bytegleich zur jeweils aktuellen Quelle. Die beiden ersten verwenden Format 620, die Zahlendatei Format 643. Sie wurden nicht als aktuelle Quellen verwendet oder gelöscht. |
| `Teil_natuerliche_Zahlen-lyxformat-620.lyx~`, `Teil_Symbole-lyxformat-620.lyx~` | Sicherungen vor der Formatumstellung. Die ältere Zahlenfassung enthält das Peano-Folgekapitel nur einmal, ab Zeile 16099. Der Formatunterschied allein ist kein Beschädigungsbefund. |
| Andere eigenständige LyX-Texte im Hauptordner | Etwa `EinfuehrungMatheBetrachtungenUeberLernen.lyx`, `lokalSuperdichteMengen.lyx`, `ueber Laengenmessung.lyx` und `UeberlegungKurven.lyx` sind hier nicht eingebunden. Sie bleiben eigenständige Texte; sie wurden nicht in die aktuelle Manuskriptfassung hineingemischt. |

Die Hauptdatei nennt noch „Version 0.1.197“ und „letzte Änderung: 07.08.2026“ [ab 186](C:/Users/marku/myCloud/Mathe/EinfuehrungMathe.lyx:186). Das beschreibt nicht den letzten Bearbeitungsstand aller Kinddokumente. Auch „aktuelle Stelle 18.08.2024“ im Zahlenteil [bei 18797](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18797) ist eine historische Arbeitsmarke, kein zuverlässiger Wegweiser zum heutigen Wiedereinstieg. Eine kleine aktuelle Standortnotiz neben dem Manuskript genügt vorerst; eine Umbenennung oder Aufräumaktion ist dafür nicht nötig.

## 3. Die beiden Peano-Folgekapitel im Einzelvergleich

Fassung A beginnt [bei 16044](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16044), Fassung B [bei 19220](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19220). Beide enthalten auch die Multiplikationsdefinition und die Handschlagaufgabe. Beide stehen im ausgegebenen Haupttext; auch die Bestands-PDF enthält beide.

Ein zeilenweiser Vergleich ergibt genau folgende Arten von Unterschieden:

1. In B erhalten fünf Labelnamen den Zusatz `-1`; die zugehörigen internen Verweise werden entsprechend angepasst.
2. B enthält acht zusätzliche leere Standardabsätze.
3. B enthält unmittelbar nach der ersten Proposition einen zusätzlichen Absatz mit `Separator plain`.

Nach dem Rückführen **nur dieser Unterschiede** stimmen die Blöcke vollständig überein, einschliesslich Formeln und Arbeitsnotizen. Es wurde also keine zweite mathematische Herleitung oder alternative Erklärung gefunden, die nur in einem der Blöcke stünde.

| Label in A | Stelle A | Entsprechendes Label in B | Stelle B |
| --- | ---: | --- | ---: |
| `prop:Addition-mit-Eins` | 16094 | `prop:Addition-mit-Eins-1` | 19270 |
| `prop:Addition-natuerlicher-Zahlen-assoziativ` | 16467 | `prop:Addition-natuerlicher-Zahlen-assoziativ-1` | 19654 |
| `lem:Peano-Eins-nicht-Nachfolger` | 17287 | `lem:Peano-Eins-nicht-Nachfolger-1` | 20486 |
| `lem:erstes-Gleichheit-von-Symbolen` | 17443 | `lem:erstes-Gleichheit-von-Symbolen-1` | 20646 |
| `lem:Gleichheit-Symbole-Aequivalenzrelation` | 17638 | `lem:Gleichheit-Symbole-Aequivalenzrelation-1` | 20845 |

**Absicht und weitere Behandlung:** Die Quelle kennzeichnet die Blöcke nicht als „Alternative“, „ältere Fassung“ oder „Wiederholung“. Der Befund passt zu einer kopierten Fassung mit angepassten Zielnamen; er beweist nicht, dass die Wiederholung unbeabsichtigt war. Deshalb ist nichts gestrichen worden.

Für eine spätere Zusammenführung wäre A technisch der einfachere Ausgangspunkt: Frühere Stellen verweisen bereits auf seine Assoziativität und sein Gleichheitslemma. Auf die fünf `-1`-Ziele in B gibt es im geprüften Verbund keine Verweise von ausserhalb B. Soll die Wiederholung bleiben, wäre eine kurze Kennzeichnung ihres Zwecks ausreichend. Soll sie entfallen, müssten vor dem Ausgliedern von B die unten genannten Gleichheitsverweise geordnet und anschliessend die Verweise erneut geprüft werden. Die beiden Blöcke sollten bei fachlichen Reparaturen jedenfalls nicht unbemerkt auseinanderlaufen.

## 4. Querverweise: Auflösung und sachliches Ziel unterscheiden

### Vollständige technische Bestandsprüfung des eingebundenen Verbunds

| Quelle | Zieldefinitionen | Verweisvorkommen | Grafikvorkommen |
| --- | ---: | ---: | ---: |
| Hauptdatei | 1 | 29 | 0 |
| Einleitung | 5 | 0 | 0 |
| Symbole | 30 | 47 | 17 |
| Logik | 873 | 2’425 | 33 |
| Mengenlehre | 91 | 511 | 15 |
| Natürliche Zahlen | 53 | 365 | 0 |
| Restposten | 99 | 359 | 5 |
| **Gesamt** | **1’152** | **3’736** | **70** |

Erfasst wurden 1’076 LyX-Label-Inserts und 76 Formel-Labels sowie 3’730 LyX-Verweise und sechs `\ref`-Vorkommen innerhalb von Formeln. Alle Zielnamen sind eindeutig; kein Verweisziel fehlt. Die 70 Grafikpfade wurden relativ zur jeweils einbindenden Quelle aufgelöst; alle 70 verschiedenen Dateien existieren. Das prüft die Pfade, nicht die spätere Grafik-Konvertierung oder die Richtigkeit einer Abbildung. Eine erst vorgemerkte Abbildung, etwa die Geogebra-Grafik [bei Zahlen 15915](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15915), ist damit nicht schon vorhanden.

**Diese technische Vollständigkeit bedeutet keine vollständige inhaltliche Prüfung aller 3’736 Verweisstellen.** Inhaltlich wurden die früher vorgemerkten Zahlenverweise, die 29 Verweisnotizen, alle 29 Verweise der Symboltabelle und die Verbindungen zu den Restposten gesichtet. Dabei sind folgende örtliche Fragen greifbar:

### Konkrete unpassende oder zu präzisierende Ziele

| Fundstelle | Befund | Örtlicher Vorschlag für eine spätere Manuskriptänderung |
| --- | --- | --- |
| [Zahlen 14503](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:14503), 14575 und 14621 | Die ersten beiden Peano-Beweise nennen die Zahlendefinition, verweisen aber auf `prop:Minimum-Teilmenge-natuerlicher-Zahlen`. Dieser Satz definiert nicht die Zahlen. | Alle drei Verweise auf `def:natuerliche-Zahlen-eigene-Definition` bei 10391 richten. |
| [Zahlen 15530](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:15530) | Der Text benötigt `m+1=1+m`, nennt Kommutation und verweist auf den späteren Assoziativitätssatz. | Auf `lem:Kommutation-n-1-natuerliche-Zahlen` bei 14229 verweisen. Alternativ den in Arbeitspaket 2 dokumentierten direkten Kürzungsweg verwenden. |
| [Zahlen 1291](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:1291), 1328, 4339, 6483, 6550, 6651, 6783, 11584, 11638 und 11689 | Diese zehn frühen Stellen verweisen auf `lem:Gleichheit-Symbole-Aequivalenzrelation` bei 17638, also auf eine spätere Induktionsübung. Das erschwert das Lesen der Grundlagenkette. | Auf das frühe `lem:Symbolgleichheit-ist-Aequivalenzrelation` bei 565 richten und dort die unabhängige Kettengrundlage aus Arbeitspaket 2 ausdrücklich benennen. Das Umhängen allein ersetzt deren Begründung nicht. |
| [Zahlen 16272](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16272) und weitere Gleichheitsverweise in A; entsprechend in B | Die Additionsbeweise verweisen auf das innerhalb desselben Folgekapitels erst später stehende Gleichheitslemma; dieses wird wiederum mit Induktion bewiesen. | Auch hier kann das frühe Gleichheitslemma die Grundlage liefern. Das spätere Lemma darf als erneute Induktionsübung bleiben. Es ist nicht nötig, den Gedanken oder die Übung zu streichen. |
| [Hauptdatei 1483](C:/Users/marku/myCloud/Mathe/EinfuehrungMathe.lyx:1483) | Die Zeile zur Potenzmenge führt auf die allgemeine aussagenlogische Mengendefinition bei Mengen 385. Die eigentliche Potenzmengendefinition steht erst bei 953 und hat dort noch kein eigenes Label. | An der vorhandenen Definition ein eigenes Label, etwa `def:Potenzmenge`, ergänzen und den Tabellenverweis dorthin richten. Keine neue Definition erforderlich. |
| [Hauptdatei 1564](C:/Users/marku/myCloud/Mathe/EinfuehrungMathe.lyx:1564) | Der Link zur „Menge der reellen Zahlen“ erreicht zwar `def:Menge-der-reellen-Zahlen`, dort steht aber eine Definition zu Folgen, nicht die angekündigte fertige Konstruktion von ℝ; siehe Restposten 28059. | Die Tabellenangabe vorläufig als Verweis auf das **Arbeitskapitel** zu reellen Zahlen kennzeichnen. Ein passender Zielname allein kann die noch auszuarbeitende Konstruktion nicht ersetzen. |
| [Hauptdatei 619](C:/Users/marku/myCloud/Mathe/EinfuehrungMathe.lyx:619) und 1525 | ℕ erscheint zweimal mit demselben Ziel im frühen Logikteil. Das Ziel ist eine vorläufige Einführung von ℕ, nicht die spätere eigene Kettenzahlendefinition. | Kein kaputter Link. Für eine eindeutige Orientierung einen Haupteintrag mit Verweis auf die eigene Zahlendefinition wählen; die frühe Einführung kann als zusätzlicher Hinweis bleiben. Ob beide Tabellenzeilen gewollt sind, bleibt offen. |
| [Hauptdatei 991](C:/Users/marku/myCloud/Mathe/EinfuehrungMathe.lyx:991) | `\bigvee` führt in das allgemeine Disjunktionskapitel. Dort wird das Zeichen tatsächlich erklärt, allerdings erst bei Logik 18495. | Ziel sachlich passend, nur ungenau. Bei Bedarf direkt an dieser Erklärung ein Label setzen. Die eigene Schreibweise wird dadurch nicht verworfen. |

Bei den übrigen Verweisen der Symboltabelle ergab sich in dieser Sichtung kein vergleichbarer Zuordnungsbedarf. Damit ist die frühere fachliche Kritik an einzelnen Quantor- oder Mengenformeln weder zurückgenommen noch nochmals als technischer Verweisfehler gezählt.

### Die 29 ausdrücklich vorgemerkten Verweisstellen

Die folgenden Zeilen bezeichnen jeweils den Anfang einer LyX-Arbeitsnotiz. Die Notiz selbst erscheint nicht im normalen Export; der umgebende Satz kann deshalb trotzdem mit einer noch unerfüllten Ankündigung stehenbleiben. „Offen“ bedeutet hier: Es wurde kein verlässlich passendes, fertig nutzbares Ziel zugeordnet. Es bedeutet nicht, dass der angekündigte Gedanke wertlos wäre oder im Skript keinen Platz haben dürfte.

| Quelle und Notizzeile | Gesuchter Anschluss | Stand bzw. nächster kleiner Schritt |
| --- | --- | --- |
| [Einleitung 1040](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Einleitung.lyx:1040) | Doppelreihensatz von Cauchy | Kein entsprechender Satz im eingebundenen Material gefunden. Das Beispiel kann als Beispiel für Nachschlagen formuliert werden; keinen internen Zielort erfinden. |
| [Einleitung 1486](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Einleitung.lyx:1486) | Kugel-/Orangenhaufen | Thematischer Anschluss in Restposten 24771 vorhanden, bislang nur als Ansatz ohne fertigen Zählbeweis. Ein Verweis darf den Ansatz ankündigen, nicht einen dort bereits abgeschlossenen Beweis. |
| [Symbole 2372](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:2372) | Sinusfunktion | Ein eigenes erklärendes Kapitel ist im eingebundenen Material nicht vorhanden. Als späterer Ausbau offen. |
| [Symbole 2607](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:2607) | Stetigkeitsdefinition | Kein entsprechendes Definitionsziel im eingebundenen Material gefunden; nicht mit der blossen Erwähnung in der Einleitung verwechseln. |
| [Symbole 3363](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:3363) | Späterer Beweis zum Zahlenbeispiel `n²<10` | Ziel noch offen; entweder den kleinen Beweis später ausarbeiten oder die Verschiebung als Arbeitsvorhaben kennzeichnen. |
| [Symbole 3432](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:3432) | Kommutativgesetz | Die Formel betrifft Multiplikation, der Text nennt Addition. Für das behauptete Multiplikationsgesetz fehlt im aktuellen Zahlen-Folgekapitel noch der systematische Beweis; siehe Arbeitspaket 5 und den möglichen Wiedereinstieg in Arbeitspaket 8. |
| [Logik 4294](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:4294) | Geordnete Paare im Zusammenhang mit ganzen Zahlen | Der Mengenteil behandelt das kartesische Produkt (`def:kartesisches-Produkt`, 15087). Eine angekündigte Konstruktion ganzer Zahlen ist damit aber noch nicht geliefert; den genauen Anspruch des Verweises trennen. |
| [Logik 4799](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:4799) | Analysis-Beispiel für einen Mengenvergleich | Noch zu wählendes Beispiel; kein bestimmtes verlorenes Label festgestellt. |
| [Logik 12147](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:12147) | `0·0=0`, `1·0=0`, `0·1=0`, `1·1=1` | Die jetzige Multiplikationsdefinition auf den positiven natürlichen Zahlen deckt die Nullfälle nicht ab. Entweder vorläufig vertraute Rechnung ausdrücklich zulassen oder die Erweiterung um 0 vorher begründen; nicht auf einen Beweis nur für positive Zahlen verlinken. |
| [Logik 12299](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:12299) | Differentialgleichungsbeispiel | Kein entsprechendes Erklärungskapitel im eingebundenen Material zugeordnet; für die Illustration des übersehenen Punktes ist eine vorweggenommene vollständige Lösung nicht erforderlich. |
| [Logik 18141](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:18141) | `0<1` | Ebenso eine Frage der Einführung von 0. Der Minimumsatz für die bei 1 beginnenden natürlichen Zahlen ist kein unmittelbarer Ersatz. |
| [Logik 18275](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:18275) | Bruchzahlen | Ein Überblick steht im Zahlbereichskapitel ab Zahlen 15645, Bruchkürzung im ggT-Abschnitt ab Restposten 873. Welcher davon passt, hängt davon ab, ob nur Beispiele oder eine begründete Einführung angekündigt werden. |
| [Logik 54226](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:54226) | Anwendung „aus Konjunktion folgt Disjunktion“ | Eine konkrete Anwendung auswählen. Die Notiz benennt noch keine eindeutige Zielstelle. |
| [Logik 94324](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:94324) | Verallgemeinerung eines logischen Minimumprinzips | Die Minimumsätze über Zahlen/Symbolketten sind thematisch verwandt, aber nicht ohne Weiteres die behauptete Verallgemeinerung über mehrere Aussagen. Ziel und gewünschte Aussage bleiben zu präzisieren. |
| [Logik 116696](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:116696) | Erklärung der Normalformen | Im Logikteil ab 146783 und ergänzend in Restposten ab 4359 vorhanden. Einen dieser unterschiedlichen Anschlüsse gezielt wählen. |
| [Logik 131553](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:131553) | Verwendung des zuvor bewiesenen Satzes | Der Text erinnert an einen früher falschen Verweis, nennt hier aber die Anwendung nicht. Ohne sichere Zuordnung bleibt die Notiz offen. |
| [Logik 263420](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:263420) | Spätere Verwendung der NAND-Substitution | Anschluss an den Erzeugenden-/Substitutionsgedanken vorhanden; eine bestimmte angekündigte Verwendung wurde noch nicht festgelegt. |
| [Mengen 17529](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:17529) | Existenz und Eindeutigkeit des Vorgängers für `n≠1` | Passender Anschluss: `lem:Vorgaenger-natuerliche-Zahl` bei Zahlen 15011. |
| [Mengen 21762](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Mengenlehre.lyx:21762) | Beispiele zur endlichen Mächtigkeit | Als kleines Beispiel die Anfangsstückmengen ab Zahlen 13120 verwenden, mit den örtlichen Berichtigungen aus Arbeitspaket 5. Die dortige Zahlen-/Mächtigkeitszuordnung nicht als unabhängige neue Zahlenkonstruktion ausgeben. |
| [Zahlen 9777](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:9777) | Vollständige Induktion | Passendes vorhandenes Ziel: `prop:vollstaendige-Induktion` bei 15230. Dies ist eine Vorschau, keine Grundlage des dort gerade vorbereiteten Minimumsatzes. |
| [Zahlen 10674](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10674) | Dezimales Stellenwertsystem | Kein abgeschlossenes Definitionskapitel zu Basis 10 zugeordnet. Das Binärrechnungsfragment ist kein Ersatz. |
| [Restposten 10902](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:10902) | Auswertung des Vergleichs `δ(A)≤δ(B)` in vier Fällen | An dieser Stelle direkt die vier Zahlenpaare `(0,0)`, `(0,1)`, `(1,0)`, `(1,1)` nennen; ein allgemeiner späterer Zahlensatz ist dafür kein notwendiger Umweg. |
| [Restposten 16065](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:16065) | Ungleichung bei Vorzeichenwechsel | Benötigt Rechen-/Ordnungsregeln auch für negative Zahlen; ein Satz nur über positive natürliche Zahlen genügt nicht. Grundlage noch ausdrücklich einzuführen oder vorauszusetzen. |
| [Restposten 27392](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27392) | Teilerfremde Bruchdarstellung im √2-Beweis | Passendes Material im eigenen ggT-Abschnitt bei 1481–1615; dort ein Ziel am berichtigten Kürzungsargument ergänzen. Siehe die geschlossene Begründung in Arbeitspaket 5, Abschnitt 8. |
| [Restposten 28611](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:28611) | Umkehrung der Grössenordnung bei positiven Kehrwerten | Entsprechende Regel für rationale Zahlen wird benötigt; kein blosses Umbenennen eines natürlichen Vergleichssatzes. |
| [Restposten 28859](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:28859) | Von `|x−a|<ε` zum Intervall um `a` | Kurzes Lemma über Betrag und Ordnung ergänzen oder die verwendete Regel ausdrücklich als vertraut voraussetzen. Ein fertiges passendes Ziel wurde nicht zugeordnet. |
| [Restposten 29679](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:29679) | Dreiecksungleichung für rationale Zahlen | Wird verwendet, hat im eingebundenen Material aber noch kein entsprechendes ausgearbeitetes Beweisziel. |
| [Restposten 29709](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:29709) | Transitivität von `≤` auf ℚ | Bereich beachten: Der vorhandene Satz über natürliche Zahlen begründet nicht bereits die rationale Ordnungsregel. |
| [Restposten 29749](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:29749) | Transitivität des Indexvergleichs `n>n₂>n₁` | Hier geht es um natürliche Indizes, nicht um die rationalen Folgenglieder. Anschluss an die Vergleichsgrundlage der natürlichen Zahlen nach ihrer bereits dokumentierten Berichtigung. |

Diese Liste erfasst die ausdrücklich mit Verweis-/Referenzhinweisen versehenen Notizen, nicht alle 602 Arbeitsnotizen und auch nicht jede beiläufige Formulierung „später“ im Skript. Wo nur ein geplanter Ausbau vorliegt, ist es für das persönliche Arbeitsmanuskript ausreichend, ihn als solchen erkennbar zu lassen.

## 5. Wie die Restposten tatsächlich eingebunden sind

`Restposten.lyx` ist kein einzelnes Kapitel mit diesem Titel. Die Hauptdatei fügt die Datei ohne eigenen Rahmentitel ein. Deshalb laufen ihre Kapitel zunächst unter dem Teil über natürliche Zahlen weiter; erst bei [27119](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Restposten.lyx:27119) beginnt der neue Teil „Die reellen Zahlen“. Die folgenden Bereiche lassen sich unterscheiden:

| Zeilenbereich | Material und heutiger Anschluss |
| --- | --- |
| 176–872 | Abschätzung des Quotienten zweier Potenzreihen: Analysis-Arbeitsstück, nicht der nächste Schritt nach der Multiplikationsdefinition. |
| 873–4358 | ggT, Minimum/Maximum, kgV sowie eine Prozentaufgabe. Die Prozentaufgabe ab 4109 besitzt keine eigene Kapitelüberschrift und steht deshalb unter kgV. Fachlich bereits in Arbeitspaket 5 mit erfasst. |
| 4359–8441 | Konjunktive/disjunktive Normalformen mit Beispielen und Tabellen. Ergänzung zum Logikteil. |
| 8442–19745 | Kronecker-/δ-Schreibweise und zahlreiche alternative Logikbeweise. Diese alternative Darstellung ist vielfach ausdrücklich angekündigt und nicht allein wegen einer bereits anderswo bewiesenen Aussage zu streichen. |
| 19746–19859 | Binäraddition als eigener, noch unfertiger Ansatz; der Beweis bricht mit „dann muss für alle“ ab. |
| 19860–24770 | Weitere Logikbeweise als Sections. Durch die derzeitige Kapitelhierarchie erscheinen sie unter „Addition zweier nicht-negativer Binärzahlen“, obwohl sie andere Sätze behandeln. |
| 24771–24820 | Orangenhaufen: persönliche Einführung und Fragestellung, noch kein ausgeführter Zählbeweis. Das ist der Anschluss an die entsprechende Erinnerung in der Einleitung. |
| 24821–25205 | Weitere NAND-Beweise als Sections. Formal stehen sie dadurch unter dem Orangenhaufen-Kapitel. |
| 25206–27118 | NAND als Implikation, Überprüfung logischer Aussagen am Computer und erste Ersetzungsregeln. Eigene logische Arbeitsstücke mit unterschiedlichen Ausarbeitungsständen. |
| 27119–28050 | Beginn des Teils „Die reellen Zahlen“, darunter Motivation und √2. Der √2-Beweis wurde in Arbeitspaket 5 örtlich geprüft. |
| 28051–30282 | Folgen-/Konvergenzmaterial im Arbeitskapitel „Was sind reelle Zahlen?“. Daraus ist noch keine abgeschlossene Konstruktion von ℝ geworden. Keine zusätzliche vollständige Analysisprüfung in diesem Arbeitspaket. |

**Die Restposten haben bereits tragende Verbindungen zum übrigen Skript:** 14 Verweisvorkommen von ausserhalb dieser Datei erreichen zehn verschiedene Ziele darin. Betroffen sind unter anderem die δ-Definition, ihre logischen Rechenformen, der Vergleich von Implikation und `≤`, Minimum/Maximum, Normalformen, die Computerprüfung und die Tabellenangabe zu ℝ. Die Datei einfach aus der Hauptdatei zu entfernen würde diese Verbindungen unterbrechen.

Für eine spätere Ordnung genügt zunächst eine Arbeitskennzeichnung dieser Bereiche. Insbesondere sollten die fremden Sections unter Binäraddition und Orangenhaufen wieder ihrem jeweiligen Logikzusammenhang zugeordnet werden. Die Alternativbeweise in δ-Schreibweise behalten dabei ihren eigenen Zweck. Weder eine endgültige Buchgliederung noch das Aufteilen aller Restposten in neue Dateien ist Voraussetzung, um wieder an einem kleinen mathematischen Anschluss weiterzuschreiben.

## 6. Konkrete, begrenzte Fortsetzung und Kontrolle

Für die Orientierung ist jetzt festgehalten:

1. Die Hauptdatei und ihre sechs Kinddokumente bleiben die Arbeitsfassung. Sicherungen, Autosaves und Exporte bleiben als unterscheidbare historische Stände erhalten.
2. Die belegten Zielverwechslungen lassen sich örtlich berichtigen. Dabei die unabhängige Gleichheitsgrundlage aus Arbeitspaket 2 beachten; ein technisch schönerer Link allein schliesst keinen Beweis.
3. Die beiden Peano-Folgekapitel bleiben bis zur bewussten Entscheidung über ihre Funktion erhalten. Ihr Variantenvergleich liegt nun vor; er muss beim Wiedereinstieg nicht erneut begonnen werden.
4. Die Restposten können als Vorrat konkreter Arbeitsstücke behandelt werden. Bestehende Querverweise müssen bei späterem Verschieben mitgeführt werden.
5. Als nächste nummerierte Aufgabe folgt Arbeitspaket 8: einen kleinen konkreten Wiedereinstieg ausarbeiten. Die vorhandene Multiplikationsdefinition bei Zahlen 18843 bzw. 22058 ist ein gut abgrenzbarer Anschluss. Das Paket soll an den vorhandenen Text anknüpfen und dessen Stimme erhalten.

**Prüfverfahren und Grenzen:** Die sieben aktiven Quellen wurden als UTF-8 gelesen, ihre Einbindungen und verschachtelten Insets ausgewertet und LyX-Verweise sowie Formel-Verweise gemeinsam aufgelöst. Arbeitsnotizen wurden von ausgegebenem Text unterschieden. Unabhängige Textzählungen bestätigten die Gesamtzahlen der Labels und Verweise. Die Kapitelblöcke wurden zeilenweise und anschliessend nach ausschliesslich den oben genannten Normalisierungen verglichen. Sicherungen und Sammelfassung wurden anhand von Inhalten, Überschriften und Labelbeständen eingeordnet, nicht bloss anhand ihrer Zeitstempel. PDF-Metadaten und extrahierter Text dienten nur dem Versionsabgleich, nicht einer Layoutprüfung.

Ein ergänzender frischer LyX-Export an einer separaten Arbeitskopie lieferte in dieser Umgebung keinen TeX-Export (Prozesscode 1 ohne Diagnoseausgabe). Deshalb wird hier **kein erfolgreicher neuer PDF-Bau** und keine vollständige Prüfung der heutigen Konverter-/LaTeX-Umgebung behauptet. Das ändert nichts an der überprüfbaren Quellen-, Pfad- und Verweisbestandsaufnahme; aus dem erfolglosen Exportversuch wird auch kein Manuskriptfehler abgeleitet.

**Arbeitspaket 7 ist als dokumentierte Sichtung abgeschlossen.** Es wurde nichts aus dem Manuskript entfernt, umbenannt oder umgeschrieben. Die Übernahme der konkreten Verweiskorrekturen und eine eventuelle Zusammenführung der Kapitel bleiben getrennte spätere Arbeitsschritte.
