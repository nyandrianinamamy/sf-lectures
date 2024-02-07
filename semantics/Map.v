Inductive partial_map (K: Type) (V: Type) :=
| Empty
| Binding (k: K) (v: V) (m: partial_map K V).