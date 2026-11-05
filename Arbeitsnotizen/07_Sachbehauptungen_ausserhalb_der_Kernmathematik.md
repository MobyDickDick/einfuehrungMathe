# Sachbehauptungen ausserhalb der Kernmathematik

Stand: 5. November 2026. Ergebnis von Arbeitspaket 6 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Grundlage sind die sechs aktuell durch `EinfuehrungMathe.lyx` eingebundenen LyX-Quellen. Fundstellen bezeichnen Quellzeilen, keine Buchseiten. Das Manuskript, seine Exporte und Sicherungen wurden nicht verändert.

## 1. Ergebnis und Reichweite

**Die deutlichsten Fehler stehen in der Schrödingergleichung und ihren Erläuterungen.** Bei Sprache, Entwicklung und Zahlengeschichte fallen vor allem unzulässige Verallgemeinerungen auf: Aus einem begrenzten Befund wird eine Aussage über alle Menschen, alle frühen Zahlen oder die gesamte Mathematik. Mehrere persönliche Vermutungen sind dagegen bereits als solche gekennzeichnet und werden hier auch so behandelt.

| Bereich | Ergebnis |
| --- | --- |
| Schrödingergleichung | Formel falsch; Betrag und Betragsquadrat, Dichte und Wahrscheinlichkeit sowie Gesamt- und Bewegungsenergie werden verwechselt. |
| Weitere Quantenvergleiche | Ununterscheidbarkeit und fehlende klassische Bahn sind verschiedene Fragen; Wahrscheinlichkeit ist kein Wahrheitswert. |
| Sprache und Schrift | „Hessisch-Deutsche“ als Grundlage der Standardsprache und die pauschale Erfindung der Lautschrift durch die Phönizier sind zu berichtigen. |
| Entwicklung | Objektpermanenz braucht eine genauere Alters- und Aufgabenangabe; die Rekapitulationsformel ist kein gültiges allgemeines Entwicklungsgesetz. |
| Wardhaugh-Erinnerung | Keine Prüfung des Buchinhalts. Drei erinnerte Aussagen sind gesondert geprüft bzw. als offen abgegrenzt. |
| Zahlengeschichte und Schulden | Wirtschaftliche Aufzeichnungen sind belegt; die universelle Entstehungsgeschichte aus Schulden, Faulheit und Geheimhaltung ist es nicht. |

Gezielt gelesen wurden die entsprechenden Passagen der Einleitung, des Symbolteils und des Zahlenteils sowie ihre Verwendungen im Logikteil. Mengenlehre und Restposten wurden nach einschlägigen Anschlüssen durchsucht. Das ist eine Prüfung der erheblichen Sachbehauptungen in diesen Themenfeldern, keine historische oder empirische Überprüfung jedes Beispiels, Witzes, Lebensberichts und jeder beiläufigen Bemerkung des gesamten Skripts. Didaktische Meinungen und politische Wertungen erhalten hier keine wissenschaftlichen Wahrheitsstempel. Die früheren mathematischen Befunde bleiben in den Arbeitspaketen 2–5 dokumentiert.

## 2. Physik: Die Schrödingergleichung und ihre Erläuterungen

### P1 – Die abgedruckte Gleichung ist falsch

**Fundstelle:** [Symbolteil, 648–671](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:648), insbesondere Formel bei 652.

Gedruckt ist, abgekürzt, `Δψ−V=Eψ`. Für ein nichtrelativistisches Teilchen ohne Magnetfeld lautet die stationäre Gleichung in kartesischen Koordinaten:

\[
-\frac{\hbar^2}{2m}\left(
\frac{\partial^2\psi}{\partial x^2}+
\frac{\partial^2\psi}{\partial y^2}+
\frac{\partial^2\psi}{\partial z^2}\right)
+V(\mathbf r)\psi(\mathbf r)=E\psi(\mathbf r).
\]

Es fehlen der kinetische Vorfaktor und der Faktor `ψ` am Potentialterm; gegenüber der üblichen Bedeutung von `V` stimmen auch die Vorzeichen nicht. Eine nicht erklärte Einheitenwahl repariert das nicht: Selbst bei `ℏ²/(2m)=1` bleibt `−Δψ+Vψ=Eψ`. Grundlage: [MIT, Zwiebach, Lecture 10, Abschnitt 1](https://live.ocw.mit.edu/courses/8-04-quantum-physics-i-spring-2016/01b09433137651bedbbfe4f039b0c5be_MIT8_04S16_LecNotes10.pdf).

Eine unmittelbare eigene Gegenprobe zeigt, weshalb der fehlende Faktor wesentlich ist: Erfüllt `ψ` die gedruckte Gleichung, dann ist bei `cψ` die linke Seite minus rechte Seite gleich `(c−1)V`. Für allgemeines `V≠0` ist also schon das blosse Multiplizieren der Wellenfunktion mit einer Konstanten keine Lösung mehr. Die richtige stationäre Gleichung ist dagegen homogen in `ψ`.

**Örtliche Reparatur:** Die richtige Formel einsetzen und ausdrücklich „zeitunabhängige Schrödingergleichung für stationäre Zustände im hier verwendeten Modell“ schreiben. Die zusätzlichen Symbole `ℏ` und `m` kurz erklären. Das Beispiel kann weiterhin zeigen, wie viel in einer Formel zusammengefasst wird.

### P2 – Betrag, Betragsquadrat und Aufenthaltswahrscheinlichkeit

**Fundstellen:** [Symbolteil, 869 ff.](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:869), besonders [948–980](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:948).

Für eine normierte räumliche Einteilchen-Wellenfunktion ist `|Ψ(r,t)|²` die **Wahrscheinlichkeitsdichte**. Für ein Raumgebiet `G` gilt

\[
P(\mathbf r\in G\text{ bei }t)=\int_G|\Psi(\mathbf r,t)|^2\,d^3r,
\qquad \int_{\mathbb R^3}|\Psi|^2\,d^3r=1.
\]

Der Betrag allein ist nicht diese Dichte. Auch die Dichte ist nicht bereits die Wahrscheinlichkeit für einen einzelnen Ort; bei einer gewöhnlichen stetigen Ortsverteilung hat ein einzelner Punkt Wahrscheinlichkeit 0. Addiert werden bei kohärenter Überlagerung die **Amplituden**; erst danach wird das Betragsquadrat gebildet. Das ergibt den Interferenzterm in `|Ψ₁+Ψ₂|²`. Grundlage: [MIT, Tokmakoff, Einführungsnotizen, Abschnitte 1.1 und Gleichung 1.12](https://ocw.mit.edu/courses/5-74-introductory-quantum-mechanics-ii-spring-2009/f61b11cc95a86973d9815f85093088db_MIT5_74s09_lec01.pdf).

**Örtliche Reparatur:** „Das Betragsquadrat gibt die Aufenthaltswahrscheinlichkeitsdichte an; über ein Gebiet aufsummiert bzw. integriert ergibt es dessen Aufenthaltswahrscheinlichkeit.“ Die komplexwertige Wellenfunktion ist mathematisch eine Funktion mit komplexen Werten, keine „Zahl, welche es eigentlich gar nicht gibt“; die Zahlbereichsfrage ist bereits in Arbeitspaket 5 behandelt.

### P3 – E ist die Gesamtenergie

**Fundstelle:** [Symbolteil, 1123–1169](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:1123).

`E` ist in der stationären Gleichung der Energieeigenwert des Hamiltonoperators, der hier kinetische und potentielle Energie zusammenfasst. Die Behauptung, es handle sich um die Bewegungsenergie, ist falsch. Grundlage: [MIT, Kärtner, Kapitel 4, Abschnitt 4.4 „Stationary States“](https://ocw.mit.edu/courses/6-974-fundamentals-of-photonics-quantum-electronics-spring-2006/235adf962a3ef4772b2f494261e00d4b_chapter4.pdf).

**Örtliche Reparatur:** „Dieser Buchstabe bezeichnet die Gesamtenergie des stationären Zustands im betrachteten Modell.“

### P4 – ∂ ist kein Delta und keine festgehaltene winzige Grösse

**Fundstellen:** [Symbolteil, 745–784](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:745) und [1018–1035](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:1018).

In der Quelle steht tatsächlich `\partial`, also `∂`. Das ist das Zeichen der partiellen Ableitung und nicht der griechische Buchstabe `δ`. Es bezeichnet hier auch keine bestimmte, beliebig kleine, aber nicht verschwindende Grösse. Die Zeichen sind beispielsweise in der [Unicode-Zeichentabelle, U+2202 „PARTIAL DIFFERENTIAL“](https://www.unicode.org/charts/PDF/U2200.pdf) unterschieden. Bei `∂ψ/∂x` werden die anderen unabhängigen Koordinaten festgehalten; siehe [MIT, Begriffserklärungen zu partiellen Ableitungen](https://ocw.mit.edu/courses/18-013a-calculus-with-applications-spring-2005/pages/study-materials/).

Die Erklärung über eine Änderung nur einer Koordinate weist in die richtige Richtung. Anschaulich kann man eine Ableitung über Differenzenquotienten mit einer von null verschiedenen Änderung `h` vorbereiten; die Ableitung ist dann deren **Grenzwert für `h→0`**, sofern er existiert. Sie entsteht nicht dadurch, dass ein einziges noch so kleines `h` festgehalten wird. Die zweite Ableitung als Änderung der ersten Ableitung zu erläutern, ist dagegen brauchbar.

### P5 – Nicht alle Lösungen sind überall klassisch differenzierbar

**Fundstelle:** [Symbolteil, 1075–1091](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:1075).

Die pauschale Gutartigkeitsaussage ist falsch, gerade auch am Wasserstoffbeispiel. Im nichtrelativistischen Coulombmodell ist die räumliche Grundzustandsfunktion `ψ(r)=C exp(−|r|/a₀)` mit positiven Konstanten `C,a₀`; siehe [MIT, Hydrogen Fine Structure, Gleichung 2.1.12](https://ocw.mit.edu/courses/8-06-quantum-physics-iii-spring-2018/439fc15f7ed10dd76c69dc3f7fea600e_MIT8_06S18ch2.pdf).

Die folgende Gegenprobe ist eine direkte Rechnung: Auf der x-Achse ist `ψ(h,0,0)=C exp(−|h|/a₀)`. Der Differenzenquotient am Ursprung hat von rechts den Grenzwert `−C/a₀` und von links `+C/a₀`. Dort existiert also bereits die erste klassische partielle Ableitung nicht. Das Coulombpotential ist an diesem Punkt ebenfalls singulär. Das widerlegt „immer“ und macht den physikalischen Zustand nicht unbrauchbar.

**Örtliche Reparatur:** Die Differenzierbarkeit vom Potential, vom Gebiet und vom verwendeten Lösungsbegriff abhängig machen. Für das Beispiel genügt: „Wo Potential und Lösung genügend regulär sind, können wir diese Ableitungen gewöhnlich auswerten; an Singularitäten ist besondere Sorgfalt nötig.“

### P6 – Quantenmechanische Quellen verhindern kein Wechselwirkungspotential

**Fundstelle:** [Symbolteil, 682–730](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:682).

Die Frage, wie das vorgegebene Potential mit ebenfalls quantenmechanischen Teilchen zusammenhängt, ist berechtigt. Falsch ist der anschliessende Schluss, dann gebe es kein Potential, mit dem gerechnet werden könne. Im nichtrelativistischen Mehrteilchenmodell kann etwa die Coulombwechselwirkung `q₁q₂/(4πε₀|r₁−r₂|)` im gemeinsamen Hamiltonoperator stehen. Die Wellenfunktion hängt dann von den Koordinaten beider Teilchen ab. Ein vorgegebenes äusseres Einteilchenpotential und eine gegenseitige Wechselwirkung sind unterschiedliche Modellierungen. Grundlage: [MIT, Kapitel 3 „Entanglement, Density Matrices, and Decoherence“, Beginn des Kapitels](https://ocw.mit.edu/courses/8-06-quantum-physics-iii-spring-2016/fc8347d83390a876ee665fbbfd9b2d7f_MIT8_06S16_chap3.pdf).

Auch die Flussanalogie braucht eine kleine Grenze: `V` bezeichnet hier potentielle Energie, ein Skalarfeld. Im konservativen klassischen Vergleich gilt `F=−∇V`; „gespeicherter Schwung“ vermischt das mit Impuls bzw. Bewegung. Eine Landkarte mit Kraftpfeilen erklärt zunächst ein Vektorfeld, noch nicht sein Potential. Als Bild kann sie bleiben, wenn der Wechsel ausdrücklich benannt wird.

### P7 – Wahrscheinlichkeit, Wahrheit und Ununterscheidbarkeit

**Fundstellen:** [Logikteil, 1706–1713](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:1706) und [37105–37168](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:37105); [Zahlenteil, 2445–2467](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:2445).

**Der Logikschluss ist falsch:** Zweiwertige Logik ist nicht der Spezialfall einer Wahrscheinlichkeitstheorie, in dem nur 0 und 1 vorkommen. Schon im klassischen Modell hat das Ereignis „Beim nächsten Wurf fällt Kopf“ eine Wahrscheinlichkeit zwischen 0 und 1, während es in jedem vollständigen Versuchsergebnis entweder eingetreten oder nicht eingetreten ist. Eine Wahrscheinlichkeit ist keine Zwischenstufe des Wahrheitswerts. Das Aischa-Beispiel beschreibt gewöhnliche Unkenntnis bzw. eine Häufigkeitsannahme; es begründet keinen quantenmechanischen Schluss. Diese Gegenprobe ist modellintern und benötigt keine bestimmte Interpretation der Quantenmechanik. Der frühere Befund zur Trennung von Nichtwissen und Negation bleibt einschlägig.

Für die Quantenpassage ist zusätzlich wichtig: Die Schrödingergleichung beschreibt die zeitliche Entwicklung des Zustands; ihre probabilistischen Messvorhersagen machen nicht jede physikalische Aussage unsicher. Der Normerhalt ist beispielsweise eine bestimmte mathematische Eigenschaft der entsprechenden Dynamik. Zur Zustandsentwicklung und Normierung siehe [MIT, Zwiebach, Quantum Physics I, Vorlesung zur Wellenfunktion und Wahrscheinlichkeitsdeutung](https://ocw.mit.edu/courses/8-04-quantum-physics-i-spring-2016/ceb707a47519f50a80034475bc7c2661_d4skxu7MpFI.pdf).

**Die Teilchenpassage vermischt zwei Dinge:** Quantenmechanische Ununterscheidbarkeit betrifft identische Teilchen derselben Art, beispielsweise Elektronen untereinander; ein Elektron und ein Proton sind unterscheidbar. Das Problem, im üblichen Quantenmodell keine bestimmte klassische Bahn zuzuweisen, besteht schon für ein einzelnes Teilchen und folgt nicht erst aus der Vertauschbarkeit mehrerer Teilchen. Die genaue Interpretation von Bahnen ist zusätzlich interpretationsabhängig. Grundlage zum Identitätsbegriff: [MIT, Zwiebach, Kapitel 8 „Identical Particles“](https://ocw.mit.edu/courses/8-06-quantum-physics-iii-spring-2018/fb48dd49e8649557f1715f0415de4f4d_MIT8_06S18ch8.pdf).

## 3. Sprache, Schrift und Entwicklung

### S1 – Standardsprache ist nicht einfach ein ausgewählter Dialekt

**Fundstelle:** [Symbolteil, 282–307](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:282).

„Hessisch-Deutsche“ als Vorbild für die deutsche Standardsprache ist sachlich falsch. Ihre Entstehung hängt mit dem Ausgleich verschiedener Schreibtraditionen zusammen, wobei ostmitteldeutsche und ostoberdeutsche Traditionen besonders wichtig waren. „Ein Dialekt wurde zur Hochsprache erklärt“ ist dafür keine hinreichende Beschreibung. Das [Leibniz-Institut für Deutsche Sprache, Sprachreport 2/2011](https://pub.ids-mannheim.de/laufend/sprachreport/pdf/sr11-2a.pdf) erläutert diese Entwicklung; die [Beschreibung von Band 89 der Studia Linguistica Germanica](https://pub.ids-mannheim.de/extern/slg/slg89.html) benennt zugleich offene historische Fragen.

**Örtliche Reparatur:** Die allgemeinen Wörter „Standardsprache“, „regionale Aussprache“ und „Dialekt“ verwenden und die falsche hessische Herkunftsangabe ersetzen. Deine persönlichen Erfahrungen mit Aussprache und Singen sind davon nicht betroffen.

### S2 – Buchstaben, Laute und die Phönizier

**Fundstellen:** [Symbolteil, 344–377](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:344), [447–481](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:447) und [3689–3695](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:3689).

Die Beobachtung, dass Laut und Schrift nicht eins zu eins zusammenpassen, stimmt. Die anschliessende Faustregel „jeder Buchstabe ein Symbol für einen Laut“ ist für das Deutsche aber zu stark: `sch` bezeichnet zusammen einen Laut, `x` gewöhnlich zwei, das Dehnungs-h keinen eigenen. Grossschreibung ist insbesondere keine allgemeine Betonungsanweisung. Die [amtlichen Grundlagen zur Laut-Buchstaben-Zuordnung](https://grammis.ids-mannheim.de/rechtschreibung/6144) beschreiben Zuordnungen zwischen Lauten und Buchstaben bzw. Buchstabengruppen. Die Kritik an Rechtschreibunterricht ist eine eigene didaktische Wertung.

Die pauschale Behauptung, die Phönizier hätten die Symbole der Lautschrift erfunden, ist historisch falsch. Phonetische Schrift und eine moderne Lautschrift sind verschiedene Begriffe; zudem gab es vor dem phönizischen Alphabet bereits alphabetische Vorläufer und andere Schriften mit Lautzeichen. Die Phönizier waren für die Weitergabe einer Konsonantenschrift an die Griechen wichtig. Siehe [Metropolitan Museum, „Alphabet Origins: From Kipling to Sinai“](https://www.metmuseum.org/exhibitions/listings/2014/assyria-to-iberia/blog/posts/alphabet) und [Scuola Normale Superiore, Mnamon: Phoenician](https://mnamon.sns.it/index.php?id=23&lang=en&page=Scrittura).

Die Kinderopfer-Passage enthält selbst eine alternative Deutung der Funde und eine noch offene Literaturangabe. Sie wird hier **nicht** als entschiedener Nachweis oder als sicher widerlegte Behauptung geführt. Für eine auszuführende historische Darstellung wären Fundort, Zeitraum und Literatur nachzutragen; für das Verständnis von Schrift liefert dieser Exkurs keine notwendige Voraussetzung.

### D1 – Objektpermanenz: Acht Monate sind keine allgemeine Untergrenze

**Fundstelle:** [Zahlenteil, 2433–2440](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:2433).

Die grundlegende Erklärung der Objektpermanenz ist brauchbar. Die Altersangabe „ab ca. 8 Monaten“ ist ohne Angabe der untersuchten Leistung irreführend. Aktives Suchen und Erwartungen, die aus Blickverhalten erschlossen werden, sind zu unterscheiden. Baillargeon und DeVos fanden bereits bei etwa 3½ bzw. 4 Monaten Hinweise darauf, dass verdeckte Gegenstände als fortbestehend repräsentiert werden. Das ersetzt nicht sämtliche anderen Leistungen durch eine neue starre Altersgrenze. Grundlage: [Baillargeon/DeVos 1991, Abstract der Originalstudie](https://pubmed.ncbi.nlm.nih.gov/1786712/).

**Örtliche Reparatur:** „Kinder entwickeln schon im ersten Lebensjahr Erwartungen über das Fortbestehen verdeckter Dinge; wann sie diese zeigen, hängt auch von der Aufgabe ab.“ Die Analogie zum Umordnen von Symbolen kann als persönliche Assoziation bleiben. Objektpermanenz ist jedoch nicht schon die Erhaltung einer Anzahl beim Umordnen und kein empirischer Beweis des Kettenlemmas.

### D2 – Piagets Kategorisierung: präzisieren, nicht pauschal als falsch streichen

**Fundstelle:** [Logikteil, 3332–3353](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:3332).

Dass Kinder schon vor den konkreten Operationen kategorisieren, ist mit einer entwicklungsbezogenen Erläuterung vereinbar. Eine vollständige Gleichsetzung mit dem logischen Umgang mit beliebigen Elementen und hierarchisch eingeschlossenen Klassen wäre dagegen zu stark. In der auf Piaget und Inhelder bezogenen Darstellung werden frühe figurale Sammlungen, spätere nichtfigurale Sammlungen und die Beherrschung hierarchischer Klasseninklusion unterschieden. Quelle: [Universität Genf, Beitrag zu Klassifikations- und Inklusionsleistungen, Abschnitt „classification or sorting skills“](https://access.archive-ouverte.unige.ch/access/metadata/1c003560-8e0a-46b3-9cd6-042f5ce01714/download).

**Einordnung:** Eine verkürzte Analogie, kein hier nachgewiesener erheblicher Einzelfehler. „Erinnert an die Entwicklung des Kategorisierens“ ist belastbarer als die Identifikation des formalen Vorgehens mit einer bestimmten Entwicklungsstufe. Die genannten Altersstufen sind auch kein Beweis für einen geeigneten Mathematiklehrgang.

### D3 – Ontogenese ist keine verkürzte Wiederholung der Stammesgeschichte

**Fundstelle:** [Zahlenteil, 10257–10272](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10257).

Die Rekapitulationsformel gehört historisch zu Haeckels biogenetischem Gesetz. In der starken Form, individuelle Entwicklung wiederhole die früheren Erwachsenenformen der Vorfahren, ist sie keine gültige allgemeine Regel. Evolutionäre Zusammenhänge zwischen Entwicklungsprozessen sind etwas anderes. Die Mathematik ist deshalb nicht eine besondere Ausnahme von einem sonst geltenden Gesetz. Zur Theorie und ihrer Kritik siehe [Arizona State University, „Ernst Haeckel's Biogenetic Law (1866)“](https://embryo.asu.edu/pages/ernst-haeckels-biogenetic-law-1866).

**Örtliche Reparatur:** Als historische Vorstellung kennzeichnen und die gewünschte pädagogische Frage direkt stellen: Muss das Lernen von Mathematik ihre Kulturgeschichte wiederholen? Eine Antwort darauf folgt weder aus Haeckels Formel noch aus ihrer Widerlegung.

### D4 – Tiere und Metasymbole bleiben eine offene, prüfbar zu formulierende These

**Fundstelle:** [Symbolteil, 3618–3659](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Symbole.lyx:3618).

Du bezeichnest die Behauptung ausdrücklich als unbewiesen und wünschst dir eine experimentelle Widerlegung. Das ist zu berücksichtigen. Sie darf nicht als gesicherte Grenzlinie zwischen Mensch und Tier verwendet werden. „Metasymbol verstehen“ müsste zuerst in eine überprüfbare Aufgabe übersetzt werden. Forschung zu symbolgestütztem analogischem Denken und zu Beziehungen zwischen Beziehungen bei Menschenaffen ist dafür relevant. Ein Beispiel ist [Flemming et al. 2008, „What Meaning Means for Same and Different“](https://pmc.ncbi.nlm.nih.gov/articles/PMC4206216/).

**Einordnung:** Diese Forschung ist kein unmittelbarer Beweis dafür, dass Tiere genau deinen Metasymbolbegriff beherrschen; sie verhindert aber den Schluss, höhere symbolische Leistungen seien durch eine allgemeine Unfähigkeitsbehauptung bereits ausgeschlossen. Die These bleibt offen. Die persönliche Wertung des Menschseins wird hier nicht naturwissenschaftlich bewertet.

## 4. Der neue Wardhaugh-Abschnitt: Leseerinnerung und Sachprüfung trennen

**Fundstelle:** [Zahlenteil, 263–309](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:263).

Du sagst ausdrücklich, dass du aus dem Gedächtnis schreibst und nicht mit dem Buch vergleichst. **Das Buch wurde auch in diesem Arbeitspaket nicht als Ganzes gelesen oder an den betreffenden Seiten nachgeprüft.** Verifiziert wurden lediglich Autor, Titel und die Identität der deutschen Ausgabe anhand der [Verlagsseite zu Wardhaughs „Zählen. Die Geschichte von den Anfängen der Mathematik“](https://www.harpercollins.de/products/zahlen-die-geschichte-von-den-anfangen-der-mathematik). Eine Verlagsbeschreibung belegt keine der drei folgenden inhaltlichen Zuschreibungen.

### W1 – Keine exakten Zahlwörter ist nicht dasselbe wie kein Mengenverständnis

Bei 281–282 steht, die Pirahã kennten offenbar gar keinen Zahlbegriff. Die Formulierung ist ohne Definition dieses Begriffs zu weit. Frank, Everett, Fedorenko und Gibson berichten 2008 das Fehlen sprachlicher Mittel für exakte Anzahlen. In sichtbaren Zuordnungsaufgaben gelangen den untersuchten Personen trotzdem genaue Zuordnungen auch grösserer Objektmengen; bei gedächtnisabhängigen Aufgaben zeigten sich Schwierigkeiten. Grundlage: [Originalstudie, Abstract](https://pubmed.ncbi.nlm.nih.gov/18547557/).

**Örtliche Reparatur:** Den konkreten Sprachbefund nennen und Mengenvergleich, exakte Zahlwörter und ein kulturell ausgebautes Zählsystem unterscheiden. Daraus folgt weder ein allgemeiner kognitiver Mangel noch, was Wardhaugh an dieser Stelle genau behauptet.

### W2 – Die Herkunft aus fernöstlichen Zählrahmen ist als Buchzuschreibung offen

Bei 283–292 wird „die Wurzel zum aktuellen Zahlensystem“ in fernöstlichen Zählrahmen verortet. Ohne den betreffenden Buchabschnitt bleibt offen, ob eine Einflusshypothese, eine bestimmte Technik oder tatsächlich ein universeller Ursprung gemeint ist. Zählrahmen, chinesische Rechenstäbchen, Stellenwert, Zahlzeichen und schriftliche Algorithmen sind nicht austauschbare Begriffe.

Die historisch übliche Darstellung führt das europäische dezimale Ziffern- und Stellenwertsystem auf indische Entwicklungen und seine Vermittlung durch die arabischsprachige Welt zurück. Sie ist kein Nachweis, dass es keine älteren oder wechselseitigen Einflüsse gegeben habe. Siehe [University of St Andrews, MacTutor: Indian numerals](https://mathshistory.st-andrews.ac.uk/HistTopics/Indian_numerals/) und [Arabic numerals](https://mathshistory.st-andrews.ac.uk/HistTopics/Arabic_numerals/).

**Einordnung:** Herkunftsbehauptung präzisieren; Wardhaugh nicht aufgrund einer erinnerten Kurzfassung widersprechen. Für einen Buchabgleich wären genaue Seiten und der Umfang der dortigen Behauptung nötig. Die Prüfung dieser Buchzuschreibung bleibt offen.

### W3 – „Kopfrechnen oder schriftliches Rechnen eigentlich nie“ ist als allgemeine Geschichte falsch

Die Aussage bei 296–309 lässt sich in ihrer weitesten Lesart bereits durch erhaltene mathematische Texte widerlegen. Der Rhind-Papyrus enthält ausgeführte Rechenverfahren und Lösungen, unter anderem zu Brüchen, Division, Multiplikation, Flächen und Volumen. Siehe [British Museum, Ausstellungshandbuch, Abschnitt „Textbook maths“, Druckseiten 144–145](https://www.britishmuseum.org/sites/default/files/2022-10/Hieroglyphs_unlocking_ancient_Egypt_large_print_guide_The_British_Museum.pdf). Das widerlegt „nie“, sagt aber noch nicht, wie häufig verschiedene Bevölkerungsteile damals im Kopf rechneten.

**Örtliche Reparatur:** „Rechenhilfen spielten in vielen Zeiten und Gesellschaften eine grössere Rolle, als ich vorher angenommen hatte.“ Falls eine bestimmte Epoche oder Benutzergruppe gemeint ist, muss sie benannt werden. Ob die Übertreibung im Buch steht oder erst beim Erinnern entstanden ist, bleibt ausdrücklich offen.

## 5. Zahlengeschichte, Schulden und historische Erzählungen

### H1 – Die kretische Geschichte verwechselt bzw. verengt die belegten Quellen

**Fundstelle:** [Zahlenteil, 10042–10097](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10042).

Die Erzählung ist als Bericht eines Kollegen gekennzeichnet; Graebers Buch wird ausdrücklich als nicht gelesen bezeichnet. Das liefert keine zusätzliche Bestätigung. Für die beschriebene Kombination aus Tempelaussenwänden, schwer entzifferbaren Zeichen und ausschliesslich privaten Schulden ist hier kein belastbarer Nachweis gefunden worden.

Ein gut belegter Bezugspunkt sind die Linear-B-Tontafeln aus der Palastverwaltung von Knossos. Das Ashmolean beschreibt beispielsweise eine Tafel mit Arbeiterinnen und Kindern; andere Aufzeichnungen betreffen Güter und Buchhaltung. Das ist mehr als eine Sammlung privater Schulden und keine Bestätigung der Wandinschriften-Erzählung. Siehe [Ashmolean Museum, „Ancient Greece“, Linear B tablet](https://www.ashmolean.org/learning-resource-ancient-greece) und [„Dining with the Minoans“, Abschnitt über die Linear-B-Aufzeichnungen](https://ashmolean.org/article/dining-with-the-minoans).

**Örtliche Reparatur:** Die Anekdote als ungesicherte Erinnerung erhalten oder durch ein konkret belegtes Verwaltungsdokument ersetzen. Nicht ohne Nachweis behaupten, nun den tatsächlichen Ursprung der mündlichen Erzählung identifiziert zu haben.

### H2 – Babylonische Schriftstücke waren nicht allgemein in einer ausgestorbenen Sprache verfasst

**Fundstelle:** [Zahlenteil, 10161–10187](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10161).

Hier werden Schrift, Sprache und soziale Zugangshürden vermischt. Keilschrift wurde für mehrere Sprachen verwendet. Sumerisch blieb nach seinem Verschwinden als gesprochene Sprache als Gelehrten- und Kultsprache in Gebrauch; das ist ein tatsächlicher Kern der Aussage. Akkadisch war dagegen ebenfalls eine Sprache der Keilschrift und wurde in der altbabylonischen Zeit gesprochen. Siehe [Oracc, Digital Corpus of Cuneiform Lexical Texts, historische Einführung](https://oracc.museum.upenn.edu/dcclt/intro/lexical_intro.html) und [Huber, „Early Linguists“, über altbabylonische sumerisch-akkadische Paradigmen](https://cdli.earth/articles/cdlp/13.1.pdf).

Der Schluss auf ein **allgemeines absichtliches Verschleiern mathematischen Wissens** folgt daraus nicht. Eine schwer zu erlernende Schreiberausbildung, gelehrte Traditionspflege, tatsächliche Zugangsbeschränkungen und bewusste Geheimhaltung sind unterschiedliche Sachverhalte. Die historische Motivzuschreibung muss eigens belegt werden.

**Örtliche Reparatur:** „Schriftliche Verwaltung und Gelehrsamkeit lagen in den Händen ausgebildeter Schreiber; dabei spielten auch ältere Sprachtraditionen eine Rolle.“ Die Kritik an heutigen Zugangshürden kann als eigene Wertung danebenstehen.

### H3 – Sachbezogene Zahlschreibungen belegen keine einzige Geburt der Zahlen aus Faulheit

**Fundstellen:** [Zahlenteil, 10145–10160](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10145) und [11344–11388](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:11344).

Unterschiedliche frühe Notations- und Masssysteme je nach gezähltem bzw. gemessenem Gegenstand sind ein ernstzunehmendes Thema. Daraus folgt aber nicht, dass man vorher keine abstrakten Anzahlen verstehen konnte und erst das Vereinheitlichen der Schrift die Zahlen entstehen liess. Zahlbegriff, gesprochenes Zahlwort, geschriebenes Zahlzeichen und Massangabe müssen unterschieden werden. Gerade die universelle Stufenfolge „konkret, dann abstrakt“ wird durch die Forschung problematisiert. Grundlage: [Valério/Ferrara, „Numeracy at the dawn of writing: Mesopotamia and beyond“, Abstract im Universitätsrepositorium](https://cris.unibo.it/handle/11585/835383).

**Einordnung:** Die Motive „Faulheit“ und geringerer Lernaufwand sind im Manuskript als Vermutung formuliert; sie sind dadurch nicht widerlegt, aber auch nicht als historische Ursache belegt. Der zugespitzte Satz über Schulden und Faulheit kann als Pointe erkennbar bleiben. Als Herkunftserklärung braucht er eine Einschränkung.

### H4 – Schulden sind belegt; daraus folgt keine alleinige Entstehungsursache der Mathematik

**Fundstellen:** [Zahlenteil, 10060–10063](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10060), [10211–10214](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10211), [10276–10285](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10276); [Logikteil, 7912–7914](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:7912) und [37351–37365](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Logik.lyx:37351).

Dass in Mesopotamien Schulden und andere wirtschaftliche Beziehungen schriftlich erfasst wurden, ist richtig. Oraccs altbabylonische Vertragsmodelle umfassen beispielsweise Darlehen, Käufe, Pacht und weitere Rechtsverhältnisse. Es handelt sich dort ausdrücklich um **Schulübungen nach Mustern tatsächlicher Verträge**, nicht selbst um durchweg vollzogene Geschäfte. Siehe [Oracc, Old Babylonian Model Contracts, Einführung](https://oracc.museum.upenn.edu/obmc/OldBabylonianModelContracts/index.html).

Zulässig ist deshalb: „Verwaltung und wirtschaftliche Verpflichtungen waren in Mesopotamien wichtige Anwendungsfelder von Zahl- und Schreibtechniken.“ Die stärkere universelle Ursprungsthese wird damit nicht belegt. Auch „Religion und Schulden waren massgebliche Triebfedern“ braucht einen benannten zeitlichen und räumlichen Bezug. Deine moralische Beurteilung von Schulden ist davon unabhängig.

### H5 – Die gesamte heutige Mathematik ist kein einzelnes Importprodukt

**Fundstelle:** [Einleitung, 1649–1653](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_Einleitung.lyx:1649).

Die Würdigung indischer und arabischsprachiger Beiträge ist berechtigt; ihre Ausdehnung auf „die Mathematik, so wir sie heute kennen“ ist zu pauschal. Eine konkrete, belegbare Aussage betrifft etwa die indischen Grundlagen und arabischsprachige Vermittlung des dezimalen Ziffern- und Stellenwertsystems nach Europa; siehe die oben genannten MacTutor-Darstellungen. Schon die ebenfalls belegte ägyptische Rechentradition zeigt, weshalb daraus keine Herkunftsangabe für **die gesamte** Mathematik werden kann.

**Örtliche Reparatur:** Den gemeinten Beitrag benennen, etwa die hier verwendete dezimale Zahlschreibweise und Rechenverfahren. Für die symbolischen Grundüberlegungen ist keine Gesamttheorie der Kulturgeschichte erforderlich.

### H6 – Die Null: historische Begriffe unterscheiden, die eigene Konvention beibehalten

**Fundstelle:** [Zahlenteil, 10719–10747](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10719).

Dein Beginn von `ℕ` bei 1 ist weiterhin zulässig. „Die Griechen und Römer hatten keine Zahl 0“ ist als Hinweis auf ihre üblichen Zahlensysteme verständlich, sollte aber nicht auf jede antike Notation ausgedehnt werden. Griechische Astronomen, insbesondere Ptolemäus, verwendeten ein Zeichen für leere Stellen in sexagesimalen Schreibungen. Ein Platzhalter und die Null als allgemein verwendete Zahl mit Rechenregeln sind verschiedene Entwicklungsleistungen. Siehe [University of St Andrews, MacTutor: Zero](https://mathshistory.st-andrews.ac.uk/HistTopics/Zero/).

**Einordnung:** Historische Präzisierung, kein Einwand gegen deine Definition und kein Zwang, die Null in `ℕ` aufzunehmen.

## 6. Zwei weitere sachliche Anschlüsse

### A1 – Mars Climate Orbiter: Der Einheitenfehler stimmt, die Wirkung ist zu genau erzählt

**Fundstelle:** [Zahlenteil, 11300–11314](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:11300).

Das Beispiel ist im Kern richtig. Der Fehler betraf Impulsdaten in Pound-force-Sekunden statt der erwarteten Newtonsekunden für die **bodenseitige Bahnberechnung**. Dadurch wurden kleine Geschwindigkeitsänderungen falsch modelliert. „Der Computer nahm zu starke Korrekturen vor“ ist keine genaue Beschreibung dieses Mechanismus. Der NASA-Bericht nennt den Faktor 4,45 und die zu niedrige Annäherungsbahn. Siehe [NASA, Mars Climate Orbiter Phase II Report, Anhang B mit dem Phase-I-Bericht, dessen Druckseiten 13 und 16–17; PDF-Seiten 70 und 73–74](https://discovery.larc.nasa.gov/discovery/PDF_FILES/mars_climate_orbiter_phaseII.pdf).

**Örtliche Reparatur:** „Unvereinbare Einheiten in den gelieferten Impulsdaten führten zu einer fehlerhaften Bahnberechnung; die Sonde kam dem Mars gefährlich nahe und ging verloren.“ Der endgültige Verbleib ist damit nicht genauer behauptet als belegt. Die Bedeutung einer Einheitenangabe lässt sich an diesem Beispiel weiterhin gut erläutern.

### A2 – Ablass: Lehre und Geldpraxis unterscheiden

**Fundstelle:** [Zahlenteil, 10230–10236](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:10230).

Die Formulierung über das Loskaufen von Sünden vermischt die Ablasslehre mit ihrer problematischen Vermarktung. In der katholischen Definition betrifft Ablass zeitliche Sündenstrafen bei bereits vergebener Schuld, nicht den Kauf der Schuldvergebung. Das belegt zunächst die Unterscheidung der Begriffe, nicht die Unschuld jeder historischen Praxis. Grundlage: [Katechismus, Nr. 1471–1473](https://www.vatican.va/content/catechism/en/part_two/section_two/chapter_two/article_4/x_indulgences.index.html). Eine historische Entstehungsgeschichte des Ablasshandels wurde hier nicht zusätzlich rekonstruiert.

**Örtliche Reparatur:** Falls der Exkurs bleibt, die Geldpraxis als solche kritisieren und nicht aus einer verkürzten Definition eine historische Kausalkette für die Entstehung der Zahlen ableiten.

## 7. Kleines Reparaturpaket und Abschluss

1. Zuerst die Schrödingerformel, `∂`, die Bedeutung von `E` und die Bornsche Dichteformel berichtigen. Diese Fehler betreffen gerade die Dinge, die das Symbolbeispiel erklären soll.
2. Die Gutartigkeitsaussage auf passende Voraussetzungen begrenzen und die Frage nach quantenmechanischen Quellen mit dem Mehrteilchenmodell beantworten.
3. Wahrscheinlichkeit und Wahrheitswert sowie Teilchenidentität und klassische Bahn auseinanderhalten. Das Aischa-Beispiel als gewöhnliches Wahrscheinlichkeitsbeispiel verwenden.
4. Die hessische Herkunftsangabe und die phönizische Alleinerfindung der Lautschrift berichtigen. Objektpermanenz, Klassifikation und Haeckels Formel sachlich eingrenzen; die Tierthese als offene These behandeln.
5. Wardhaugh weiterhin als Leseerinnerung führen. Pirahã präzisieren, „nie“ beim schriftlichen Rechnen zurücknehmen und die konkrete Herkunftszuschreibung bis zu einem Seitenabgleich offenlassen.
6. In der Zahlengeschichte konkrete Quellen, begrenzte Sachbefunde, ungesicherte Anekdoten und persönliche Deutungen unterscheiden. Insbesondere die allgemeinen Aussagen über babylonische Sprachen, Geheimhaltung und die Entstehung aller Zahlen eingrenzen. Marsbeispiel und Ablassbegriffe örtlich präzisieren.

Die Quellen wurden am 5. November 2026 online recherchiert; direkt verlinkt sind jeweils die einschlägigen institutionellen Darstellungen, Vorlesungsunterlagen oder Forschungsarbeiten. Bei Pirahã und den frühen Objektpermanenzbefunden wurde insbesondere der Abstract der Originalstudie ausgewertet; daraus wird keine vollständige Neubewertung des Forschungsgebiets behauptet. Der Piaget-Abschnitt stützt sich auf eine wissenschaftliche Darstellung aus dem Genfer Repositorium, nicht auf eine vorgetäuschte Lektüre des gesamten Originalwerks. Die Rechnungen zur Homogenität und zum Wasserstoff-Grundzustand sind oben eigenständig angegeben. Ein numerisches Experiment könnte weder eine historische Ursprungsthese noch eine universelle empirische Behauptung beweisen und wurde dafür nicht angesetzt.

**Arbeitspaket 6 ist damit als dokumentierte Sachprüfung abgeschlossen.** Offene Buch- und Literaturabgleiche sind als offen benannt; ihre Ergebnisse wurden nicht erfunden. Die Übernahme der örtlichen Reparaturen ins Manuskript bleibt ein eigener Schritt. Das nächste nummerierte Arbeitspaket ist **7: Manuskriptaufbau und technische Altlasten sichten**.
