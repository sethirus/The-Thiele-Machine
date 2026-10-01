# Parts 5--7 scope-note amendment

Date: 2026-10-01

The first full gate correctly required the new standalone real-system models
to carry the repository's explicit `SCOPE NOTE: standalone proof scope` marker
instead of importing unused VM modules. Adding those comments changes byte
hashes but changes no Coq token after comment erasure, definition, statement,
or proof. The original dated freezes remain the semantic preregistration; this
record prevents anyone from mistaking the later byte hashes for silent target
changes.

Post-comment target SHA-256 values:

- RFC9162MerkleTarget.v: `ac5e60d93103f9312462919e59cd98c8e0486ab99393e4f74fc9b84c6a900a61`
- NeculaPCCTarget.v: `8aacb49264c186f9aa7c8dbe8a86aada77c4c6740e1fe255b8151a71c56d0ebc`
- ConcreteRecordMachinesTarget.v: `f50aa8fe1392f4f905c07e5a6ccbed91bb1e79d714f8306fafd2a7884ba83e99`
- ConcreteRAMTarget.v: `7bd79747eb82a319258055633ee434716b9bb27f2ae5fd80c8ccf922cd31cd11`
- TPMQuoteAuthenticityTarget.v: `118def4da9b9ff55bad5245e8b6f46f8b1b854b00d3ad41240605de679faf6a8`
- RecordProliferationSurveyTarget.v: `8cf4a135ac3e16afcf5dfa928c80c8ff6554a10e6426977c1fa955d28e04c5b9`
- RealSystemConsequencesTarget.v: `306db0519f3427ed7959ad70746d38ee8b29672cb17494b97e4d578c6ab59e9e`

Call made: use the documented, source-local standalone-scope declaration. Do
not add fake VM imports and do not exempt files by weakening the connectivity
gate.

