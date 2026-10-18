# Calibration inputs (third-party data)

These two files are by John Seamons and come unchanged from his Zenodo record, "A 39-Crossing Venn Diagram of
Order Eight" (19 August 2026), https://doi.org/10.5281/zenodo.22004839, licensed CC BY 4.0
(https://creativecommons.org/licenses/by/4.0/). They are redistributed here under that licence.

| file | crossings | what it is | sha256 |
|---|---|---|---|
| `venn8_39_crossing_candidate.json` | 39 | Seamons's 39-crossing 8-Venn diagram | `ad016b8106c66ef67f37b636a5c1b40627398f4f700746ecff854dd9f0815222` |
| `venn8_40_source_variant030.json` | 40 | Seamons's machine-readable reconstruction of the 40-crossing 8-Venn diagram of Brenner, Gregor, Mütze and Verciani (SoCG 2026), variant 30 | `db61a35ad8d38400ca56f5c5cbe4f662c4a04a4a81afe0db98f93155e7b41108` |

They are used only to calibrate the checkers in `../checkers/`: every checker must accept both, and must reject
each with one face removed. The results are in `../logs/`.
