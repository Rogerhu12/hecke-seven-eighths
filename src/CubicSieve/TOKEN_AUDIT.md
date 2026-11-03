# Token usage audit

Period: 2026-10-30 16:48:41 to 18:39:21 Asia/Taipei (before the user accounting question).

Output counts are actual deduplicated token_usage_record usage for each actor. Output includes reasoning; nonreasoning output is also shown. Earlier descent work is excluded.

Lean source tokens are an o200k_base estimate after removing nested block comments and line comments. Compiled source means successful receipt, matching source SHA256 and existing olean, not completion of the requested theorem. Modules are attributed to their first source-creation writer; copied Algebra/Iteration are assigned to root.

| Agent | Output | Of which reasoning | Compiled Lean tokens | Output / compiled | Nonreason / compiled |
|---|---:|---:|---:|---:|---:|
| root | 175,425 | 89,773 | 23,368 | 7.51 | 3.67 |
| /root/artin_factors | 144,275 | 65,728 | 15,237 | 9.47 | 5.16 |
| /root/pole_matching | 147,241 | 86,495 | 18,365 | 8.02 | 3.31 |
| /root/euler_audit | 166,907 | 74,278 | 40,421 | 4.13 | 2.29 |

All actors output: 633,848; compiled Lean source estimate: 97,391; ratio 6.51.
Including uncompiled drafts gives 141,847 source tokens and ratio 4.47.

The final MI-M-CUBIC-SIEVE theorem remains unfinished. These are auxiliary-code productivity ratios, not a theorem completion metric.
