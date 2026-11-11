# Erste örtliche Übernahme ins Manuskript

Stand: 11. November 2026. Ergebnis von Arbeitspaket 12 aus der [Aufgabenliste](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Aufgabenliste.md). Markus hat die vorgeschlagene örtliche Übernahme des korrigierten Additionskommutativitätsbeweises und des ersten kleinen Multiplikationsabschnitts ausdrücklich beauftragt. Anders als die bisherigen Prüfungen und Schreibentwürfe verändert dieses Paket die aktuelle LyX-Quelle.

## 1. Umfang und Auswahl

Geändert wurde ausschliesslich [Teil_natuerliche_Zahlen.lyx](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx). Grundlage sind [06, Abschnitte 2–4](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/06_Rechnen_und_Zahlbereiche.md) und [09, Abschnitte 1–3](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/09_Wiedereinstieg_Multiplikation.md).

Für die Addition wurde die vorgeschlagene Induktionsvariante gewählt. Sie passt zum ausdrücklich vorhandenen Wunsch, die vollständige Induktion weiter zu üben. Für die Multiplikation wurde der in 09 benannte erste Haltepunkt gewählt: der vollständige Beweis von \(m\cdot1=m\). Die beiden anschliessenden Beweise aus 09 sind noch nicht übernommen.

Beide ausgegebenen Peano-Folgekapitel erhalten dieselben fachlichen Änderungen. Damit laufen die wiederholten Stellen nicht auseinander. Die Kapitel wurden weder zusammengeführt noch entfernt; ihre beabsichtigte Funktion bleibt die in [08, Abschnitt 3](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/08_Manuskriptaufbau_und_technische_Altlasten.md) dokumentierte offene Frage. Persönliche Beispiele und die übrigen Abschnitte wurden beibehalten. Hauptdatei, Bestands-PDF, ältere TeX-Exporte, Sicherungen und Autosaves wurden nicht verändert.

## 2. Geänderte Stellen

Die folgenden Zeilen beziehen sich auf die Quelle **nach dieser Übernahme**. Ältere Arbeitsnotizen bleiben datierte Befunde mit ihren damaligen Zeilenangaben.

| Änderung | Erstes Kapitel | Wiederholtes Kapitel |
| --- | --- | --- |
| Örtliche Voraussetzung: festes nichtleeres Grundsymbol, feste Zerlegung, endlicher Aufbau, vollständige und eindeutige Benennung der Ketten, Abschluss der Addition und Induktion ab 1 | [16067](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16067) | [19268](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19268) |
| Assoziativität: Anwendung des Nachfolgersatzes statt fälschlich genannter Induktionsvoraussetzung | [16571](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:16571) | [19783](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:19783) |
| Direkter Assoziativitätsbeweis: unterschiedliche Gruppierungen in der letzten Kettengleichung; ausdrücklicher Rückschluss auf Zahlengleichheit | [17021](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17021) | [20237](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:20237) |
| Vollständiger Ersatzbeweis der Additionskommutativität ohne Subtraktion | [17112](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:17112) | [20332](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:20332) |
| Neuer Abschnitt „Die Eins als zweiter Faktor“, mit Rekursionsgrundlage, Unterscheidung von Ketten- und Zahlenmultiplikation sowie Lemma und Induktionsbeweis | [18790](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:18790) | [22030](C:/Users/marku/myCloud/Mathe/EinfuehrungMatheBuchTeile/Teil_natuerliche_Zahlen.lyx:22030) |

Die beiden Korrekturen der Assoziativität gehören zu den örtlichen Voraussetzungen des gewählten Additionsbeweises. Der Ersatzbeweis hält \(n_1\) beliebig fest und induziert über \(n_2\). Der Anfang ist \(n_1+1=1+n_1\); im Schritt werden der Nachfolgersatz, die Induktionsannahme, das frühere Lemma zur Kommutation mit 1 und die bereits behandelte Assoziativität verwendet. Allgemeine Additionskommutativität wird dabei nicht vorausgesetzt. Die bisherigen falschen Zwischenformeln und die vorzeitig verwendeten Differenzen entfallen an beiden Stellen.

Bei \(m\cdot1=m\) wird über den ersten Faktor \(m\) induziert. Anfang und Schritt folgen genau aus \(1\cdot n=n\) und \((m+1)\cdot n=m\cdot n+n\). Es wird weder ein Faktor vertauscht noch ein Multiplikationsgesetz vorweggenommen. Der folgende Handschlagabschnitt bleibt als vorhandener Anschluss erhalten.

## 3. Voraussetzungen und verbleibende Grenzen

Die Ketten- und Induktionsgrundlage wird für diese Rechenbeweise ausdrücklich vorausgesetzt. Der neue Absatz ist keine nachträgliche Schliessung sämtlicher früherer Grundlagenbeweise. Insbesondere bleiben das Anfangsstücklemma, die Reparatur des Minimumbeweises und die früher dokumentierten ausgelassenen Schritte aus [03](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/03_Begruendungskette_natuerliche_Zahlen.md) als Übernahmearbeiten offen. Die neue Multiplikationserläuterung benennt entsprechend die endliche Rekursion als Grundlage und erläutert Existenz durch endlichen Aufbau und Eindeutigkeit durch Induktion.

Noch nicht übernommen sind der Nachfolgersatz im zweiten Faktor und die Multiplikationskommutativität aus 09 sowie die Fortsetzungen aus 10–12. Der Handschlagbeweis braucht weiterhin die bereits dokumentierte örtliche Formelkorrektur und die gesonderte Behandlung von Subtraktion und Division. Die jetzige Übernahme behauptet deshalb keine vollständige Reparatur des Zahlenteils oder des ganzen Manuskripts.

## 4. Prüfungen

Die ausgeschriebenen Beweise wurden auf Anfang bei 1, Induktionsvariable, festgehaltene Parameter und die Grundlage jeder Umformung geprüft. Der Additionsbeweis setzt keine Subtraktion voraus; der Multiplikationsbeweis benutzt kein noch unbewiesenes Multiplikationsgesetz.

Die LyX-Quelle ist weiterhin UTF-8 mit den vorhandenen CRLF-Zeilenenden und Format 643. Layouts und Insets sind korrekt verschachtelt. Im Verbund der Hauptdatei und ihrer sechs Kinddokumente sind alle **1’152 Zielnamen eindeutig** und sämtliche **3’740 Verweisvorkommen aufgelöst**. Der Vergleich der beiden Peano-Folgekapitel ergibt nach ausschliesslicher Normalisierung der schon dokumentierten fünf Labelvarianten, leeren Absätze und des Separators weiterhin gleichen Text und gleiche Formeln.

Ein frischer LyX-Export einer separaten Quellenkopie und zwei anschliessende pdfLaTeX-Läufe waren erfolgreich. Der isolierte Zahlenteil ergibt 118 PDF-Seiten. Dabei fehlen naturgemäss Verweisziele aus anderen Buchteilen; das ist von der vollständigen technischen Verweisprüfung im Quellenverbund zu unterscheiden. Die fünf gemeldeten überbreiten Zeilen liegen ausserhalb der geänderten Abschnitte. Die geänderten Beweise, Assoziativitätskorrekturen und die Übergänge zur Handschlagaufgabe wurden in gerenderten Seiten visuell geprüft. Der [Prüfauszug](C:/Users/marku/myCloud/Mathe/Arbeitsnotizen/Pruefausgaben/12_Erste_Uebernahme_Pruefauszug.pdf) enthält ausgewählte Seiten der separaten Ausgabe; seine Seitennummern sind keine Buchseiten der bisherigen Gesamtausgabe. Ein frischer Bau des gesamten Buchs und eine maschinelle Formalisierung sind damit nicht behauptet.

## 5. Abschluss und nächstes dokumentiertes Paket

**Arbeitspaket 12 ist abgeschlossen.** Der Additionskommutativitätsbeweis ist örtlich ersetzt, die beiden einschlägigen Assoziativitätskorrekturen sind mitgeführt, und der erste Multiplikationsabschnitt bis \(m\cdot1=m\) ist in beiden Peano-Folgekapiteln übernommen und geprüft.

**Arbeitspaket 13: Den Multiplikationsanschluss aus 09 bis zur Kommutativität übernehmen.** Direkt nach dem jetzt eingefügten Abschnitt sind zuerst \(m\cdot(n+1)=m\cdot n+m\) und danach \(m\cdot n=n\cdot m\) mit den vorbereiteten vollständigen Induktionsbeweisen einzufügen. Die örtlich vorausgesetzte Ketten-, Induktions- und Rekursionsgrundlage bleibt ausdrücklich benannt. Beide Kapitel sind fachlich gleich nachzuführen; neue Verweise sind zu prüfen und die geänderten Abschnitte separat zu exportieren und visuell zu kontrollieren. Haltepunkt ist die Multiplikationskommutativität. Dieses nächste Paket ist dokumentiert, aber noch nicht ausgeführt.
