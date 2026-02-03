import Starstream.Oracle.Idealized

set_option autoImplicit false

namespace Starstream.Oracle

private def enumFrom {α : Type} (start : Nat) (xs : List α) : List (Nat × α) :=
  match xs with
  | [] => []
  | x :: xs => (start, x) :: enumFrom (start + 1) xs

private def applyChunkStep
    (cfg : Config) (gasPerTx : Gas) (acc : Except ChunkErr Ledger) (p : Nat × Tx) :
    Except ChunkErr Ledger :=
  match acc with
  | .ok lcur =>
      match applyTx cfg lcur p.2 gasPerTx with
      | .ok lnext => .ok lnext
      | .error err => .error (ChunkErr.txError p.1 err)
  | .error e => .error e

private def applyChunkFrom
    (cfg : Config) (idx : Nat) (l : Ledger) (txs : List Tx) (gasPerTx : Gas) :
    Except ChunkErr Ledger :=
  let rec go (idx : Nat) (lcur : Ledger) (rest : List Tx) : Except ChunkErr Ledger :=
    match rest with
    | [] => .ok lcur
    | tx :: tail =>
        match applyTx cfg lcur tx gasPerTx with
        | .ok lnext => go (idx + 1) lnext tail
        | .error err => .error (ChunkErr.txError idx err)
  go idx l txs

private def applyChunkFoldFrom
    (cfg : Config) (idx : Nat) (l : Ledger) (txs : List Tx) (gasPerTx : Gas) :
    Except ChunkErr Ledger :=
  (enumFrom idx txs).foldl (applyChunkStep cfg gasPerTx) (.ok l)

private theorem foldl_step_error
    {cfg : Config} {gasPerTx : Gas} {e : ChunkErr} {idx : Nat} {txs : List Tx} :
    List.foldl (applyChunkStep cfg gasPerTx) (.error e) (enumFrom idx txs) = .error e := by
  induction txs generalizing idx with
  | nil => rfl
  | cons tx tail ih =>
      simp only [enumFrom, List.foldl_cons, applyChunkStep, ih]

private theorem applyChunkFrom_go_eq_fold
    {cfg : Config} {gasPerTx : Gas} {idx : Nat} {l : Ledger} {txs : List Tx} :
    applyChunkFrom.go cfg gasPerTx idx l txs =
      (enumFrom idx txs).foldl (applyChunkStep cfg gasPerTx) (.ok l) := by
  induction txs generalizing idx l with
  | nil => rfl
  | cons tx tail ih =>
      simp only [applyChunkFrom.go, enumFrom, List.foldl_cons, applyChunkStep]
      cases applyTx cfg l tx gasPerTx with
      | ok lnext => exact ih
      | error err => exact foldl_step_error.symm

private theorem applyChunkFrom_eq_fold
    {cfg : Config} {idx : Nat} {l : Ledger} {txs : List Tx} {gasPerTx : Gas} :
    applyChunkFrom cfg idx l txs gasPerTx =
      applyChunkFoldFrom cfg idx l txs gasPerTx := by
  simpa [applyChunkFrom, applyChunkFoldFrom] using
    (applyChunkFrom_go_eq_fold (cfg := cfg) (gasPerTx := gasPerTx) (idx := idx) (l := l) (txs := txs))

private theorem applyChunk_go_eq_fold
    {cfg : Config} {gasPerTx : Gas} {idx : Nat} {l : Ledger} {txs : List Tx} :
    applyChunk.go cfg gasPerTx idx l txs =
      (enumFrom idx txs).foldl (applyChunkStep cfg gasPerTx) (.ok l) := by
  induction txs generalizing idx l with
  | nil => rfl
  | cons tx tail ih =>
      simp only [applyChunk.go, enumFrom, List.foldl_cons, applyChunkStep]
      cases applyTx cfg l tx gasPerTx with
      | ok lnext => exact ih
      | error err => exact foldl_step_error.symm

private theorem applyChunk_go_ok_prefix
    {cfg : Config} {gasPerTx : Gas} {idx : Nat} {l : Ledger} {txs : List Tx} {l' : Ledger} :
    applyChunk.go cfg gasPerTx idx l txs = .ok l' ->
    ∀ j : Nat, j ≤ txs.length ->
      ∃ l'', applyChunk.go cfg gasPerTx idx l (txs.take j) = .ok l'' := by
  induction txs generalizing idx l with
  | nil =>
      intro h j hj
      cases j with
      | zero =>
          refine ⟨l, ?_⟩
          simp [applyChunk.go]
      | succ j =>
          cases (Nat.not_succ_le_zero j hj)
  | cons tx tail ih =>
      intro h j hj
      cases hTx : applyTx cfg l tx gasPerTx with
      | error err =>
          simp [applyChunk.go, hTx] at h
      | ok lnext =>
          have htail : applyChunk.go cfg gasPerTx (idx + 1) lnext tail = .ok l' := by
            simpa [applyChunk.go, hTx] using h
          cases j with
          | zero =>
              refine ⟨l, ?_⟩
              simp [applyChunk.go]
          | succ j =>
              have hj' : j ≤ tail.length := by
                simpa using (Nat.succ_le_succ_iff.mp hj)
              rcases ih (idx := idx + 1) (l := lnext) htail j hj' with
                ⟨l'', hprefix⟩
              refine ⟨l'', ?_⟩
              simp [applyChunk.go, List.take, hTx, hprefix]

private theorem applyChunk_go_first_error
    {cfg : Config} {gasPerTx : Gas} {idx : Nat} {l : Ledger} {txs : List Tx}
    {i : Nat} {err : Err} :
    applyChunk.go cfg gasPerTx idx l txs = .error (ChunkErr.txError i err) ->
    ∃ pre tx tail l',
      txs = pre ++ tx :: tail ∧
      pre.length + idx = i ∧
      applyChunk.go cfg gasPerTx idx l pre = .ok l' ∧
      applyTx cfg l' tx gasPerTx = .error err := by
  induction txs generalizing idx l with
  | nil =>
      intro h
      simp [applyChunk.go] at h
  | cons tx tail ih =>
      intro h
      cases hTx : applyTx cfg l tx gasPerTx with
      | ok lnext =>
          have h' :
              applyChunk.go cfg gasPerTx (idx + 1) lnext tail =
                .error (ChunkErr.txError i err) := by
            simpa [applyChunk.go, hTx] using h
          rcases ih (idx := idx + 1) (l := lnext) h' with
            ⟨pre, tx', tail', l', htxs, hlen, hok, hfail⟩
          refine ⟨tx :: pre, tx', tail', l', ?_, ?_, ?_, hfail⟩
          · simp [htxs]
          ·
            calc
              (List.length (tx :: pre)) + idx
                  = (pre.length + 1) + idx := by
                      simp
              _ = pre.length + (1 + idx) := by
                    simpa using (Nat.add_assoc pre.length 1 idx)
              _ = pre.length + (idx + 1) := by
                    simp [Nat.add_comm]
              _ = i := hlen
          ·
            simpa [applyChunk.go, hTx] using hok
      | error err0 =>
          have h' :
              (Except.error (ChunkErr.txError idx err0) : Except ChunkErr Ledger) =
                (Except.error (ChunkErr.txError i err) : Except ChunkErr Ledger) := by
            simpa [applyChunk.go, hTx] using h
          cases h'
          refine ⟨[], tx, tail, l, ?_, ?_, ?_, ?_⟩
          · simp
          · simp
          · simp [applyChunk.go]
          · simp [hTx]

private theorem take_append_length {α : Type} (pre rest : List α) :
    (pre ++ rest).take pre.length = pre := by
  induction pre with
  | nil => simp
  | cons x xs ih =>
      simp [List.length, ih]

private theorem take_append_of_le_length {α : Type} (pre rest : List α) (j : Nat) :
    j ≤ pre.length -> (pre ++ rest).take j = pre.take j := by
  intro hj
  induction pre generalizing j with
  | nil =>
      have : j = 0 := Nat.eq_zero_of_le_zero hj
      simp [this]
  | cons x xs ih =>
      cases j with
      | zero => simp
      | succ j =>
          have hj' : j ≤ xs.length := by
            simpa using (Nat.succ_le_succ_iff.mp hj)
          simp [List.take, ih j hj']

private theorem drop_append_length {α : Type} (pre rest : List α) :
    (pre ++ rest).drop pre.length = rest := by
  induction pre with
  | nil => simp
  | cons x xs ih =>
      simp [List.length, ih]

def _root_.List.get? {α : Type} : List α -> Nat -> Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ n => get? xs n

private theorem get?_eq_head?_drop {α : Type} (xs : List α) (i : Nat) :
    xs.get? i = (xs.drop i).head? := by
  induction xs generalizing i with
  | nil =>
      cases i <;> rfl
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa using ih (i := i)

theorem applyChunk_fold
    {cfg : Config} {l : Ledger} {txs : List Tx} {gasPerTx : Gas} :
    applyChunk cfg l txs gasPerTx =
      applyChunkFoldFrom cfg 0 l txs gasPerTx := by
  simpa [applyChunk, applyChunkFoldFrom] using
    (applyChunk_go_eq_fold (cfg := cfg) (gasPerTx := gasPerTx) (idx := 0) (l := l) (txs := txs))

theorem applyChunk_first_error
    {cfg : Config} {l : Ledger} {txs : List Tx} {gasPerTx : Gas}
    {idx : Nat} {err : Err} :
    applyChunk cfg l txs gasPerTx = .error (ChunkErr.txError idx err) ->
    ∃ pre tx tail l',
      txs = pre ++ tx :: tail ∧
      pre.length = idx ∧
      applyChunk cfg l pre gasPerTx = .ok l' ∧
      applyTx cfg l' tx gasPerTx = .error err := by
  intro h
  have h' :
      applyChunk.go cfg gasPerTx 0 l txs =
        .error (ChunkErr.txError idx err) := by
    simpa [applyChunk] using h
  rcases applyChunk_go_first_error (cfg := cfg) (gasPerTx := gasPerTx)
      (idx := 0) (l := l) (txs := txs) h' with
    ⟨pre, tx, tail, l', htxs, hlen, hok, hfail⟩
  refine ⟨pre, tx, tail, l', htxs, ?_, ?_, hfail⟩
  · simpa using hlen
  · simpa [applyChunk] using hok

theorem applyChunk_first_error_take
    {cfg : Config} {l : Ledger} {txs : List Tx} {gasPerTx : Gas}
    {idx : Nat} {err : Err} :
    applyChunk cfg l txs gasPerTx = .error (ChunkErr.txError idx err) ->
    ∃ l', applyChunk cfg l (txs.take idx) gasPerTx = .ok l' := by
  intro h
  rcases applyChunk_first_error (cfg := cfg) (l := l) (txs := txs) (gasPerTx := gasPerTx) h with
    ⟨pre, tx, tail, l', htxs, hlen, hok, hfail⟩
  have htake : txs.take idx = pre := by
    simp [htxs, hlen]
  refine ⟨l', ?_⟩
  simp [htake, hok]

theorem applyChunk_first_error_prefix_ok
    {cfg : Config} {l : Ledger} {txs : List Tx} {gasPerTx : Gas}
    {idx : Nat} {err : Err} :
    applyChunk cfg l txs gasPerTx = .error (ChunkErr.txError idx err) ->
    ∀ j : Nat, j < idx ->
      ∃ l', applyChunk cfg l (txs.take j) gasPerTx = .ok l' := by
  intro h j hj
  rcases applyChunk_first_error (cfg := cfg) (l := l) (txs := txs) (gasPerTx := gasPerTx) h with
    ⟨pre, tx, tail, l', htxs, hlen, hok, hfail⟩
  have hj' : j ≤ pre.length := by
    have : j < pre.length := by simpa [hlen] using hj
    exact Nat.le_of_lt this
  have hok' : applyChunk.go cfg gasPerTx 0 l pre = .ok l' := by
    simpa [applyChunk] using hok
  rcases applyChunk_go_ok_prefix (cfg := cfg) (gasPerTx := gasPerTx)
      (idx := 0) (l := l) (txs := pre) hok' j hj' with
    ⟨l'', hprefix⟩
  have htake : txs.take j = pre.take j := by
    have htake' : (pre ++ tx :: tail).take j = pre.take j :=
      take_append_of_le_length (pre := pre) (rest := tx :: tail) (j := j) hj'
    simpa [htxs] using htake'
  refine ⟨l'', ?_⟩
  have : applyChunk cfg l (pre.take j) gasPerTx = .ok l'' := by
    simpa [applyChunk] using hprefix
  simpa [htake] using this

theorem applyChunk_first_error_prefix_ok_le
    {cfg : Config} {l : Ledger} {txs : List Tx} {gasPerTx : Gas}
    {idx : Nat} {err : Err} :
    applyChunk cfg l txs gasPerTx = .error (ChunkErr.txError idx err) ->
    ∀ j : Nat, j ≤ idx ->
      ∃ l', applyChunk cfg l (txs.take j) gasPerTx = .ok l' := by
  intro h j hj
  cases Nat.lt_or_eq_of_le hj with
  | inl hlt =>
      exact applyChunk_first_error_prefix_ok (cfg := cfg) (l := l) (txs := txs)
        (gasPerTx := gasPerTx) h j hlt
  | inr hEq =>
      rcases applyChunk_first_error_take (cfg := cfg) (l := l) (txs := txs)
          (gasPerTx := gasPerTx) h with
        ⟨l', hok⟩
      refine ⟨l', ?_⟩
      simpa [hEq] using hok

theorem applyChunk_first_error_drop
    {cfg : Config} {l : Ledger} {txs : List Tx} {gasPerTx : Gas}
    {idx : Nat} {err : Err} :
    applyChunk cfg l txs gasPerTx = .error (ChunkErr.txError idx err) ->
    ∃ tx tail l',
      txs.drop idx = tx :: tail ∧
      applyChunk cfg l (txs.take idx) gasPerTx = .ok l' ∧
      applyTx cfg l' tx gasPerTx = .error err := by
  intro h
  rcases applyChunk_first_error (cfg := cfg) (l := l) (txs := txs) (gasPerTx := gasPerTx) h with
    ⟨pre, tx, tail, l', htxs, hlen, hok, hfail⟩
  have hdrop : txs.drop idx = tx :: tail := by
    simp [htxs, hlen]
  have htake : txs.take idx = pre := by
    simp [htxs, hlen]
  refine ⟨tx, tail, l', hdrop, ?_, hfail⟩
  simpa [htake] using hok

theorem applyChunk_first_error_head?_drop
    {cfg : Config} {l : Ledger} {txs : List Tx} {gasPerTx : Gas}
    {idx : Nat} {err : Err} :
    applyChunk cfg l txs gasPerTx = .error (ChunkErr.txError idx err) ->
    ∃ tx l',
      List.head? (txs.drop idx) = some tx ∧
      applyChunk cfg l (txs.take idx) gasPerTx = .ok l' ∧
      applyTx cfg l' tx gasPerTx = .error err := by
  intro h
  rcases applyChunk_first_error_drop (cfg := cfg) (l := l) (txs := txs)
      (gasPerTx := gasPerTx) h with
    ⟨tx, tail, l', hdrop, hok, hfail⟩
  refine ⟨tx, l', ?_, hok, hfail⟩
  simp [hdrop]

theorem applyChunk_first_error_get?
    {cfg : Config} {l : Ledger} {txs : List Tx} {gasPerTx : Gas}
    {idx : Nat} {err : Err} :
    applyChunk cfg l txs gasPerTx = .error (ChunkErr.txError idx err) ->
    ∃ tx l',
      txs.get? idx = some tx ∧
      applyChunk cfg l (txs.take idx) gasPerTx = .ok l' ∧
      applyTx cfg l' tx gasPerTx = .error err := by
  intro h
  rcases applyChunk_first_error_drop (cfg := cfg) (l := l) (txs := txs)
      (gasPerTx := gasPerTx) h with
    ⟨tx, tail, l', hdrop, hok, hfail⟩
  have hget : txs.get? idx = some tx := by
    calc
      txs.get? idx = (txs.drop idx).head? := get?_eq_head?_drop (xs := txs) (i := idx)
      _ = some tx := by simp [hdrop]
  refine ⟨tx, l', hget, hok, hfail⟩

theorem applyChunk_first_error_index_lt_length
    {cfg : Config} {l : Ledger} {txs : List Tx} {gasPerTx : Gas}
    {idx : Nat} {err : Err} :
    applyChunk cfg l txs gasPerTx = .error (ChunkErr.txError idx err) ->
    idx < txs.length := by
  intro h
  rcases applyChunk_first_error (cfg := cfg) (l := l) (txs := txs) (gasPerTx := gasPerTx) h with
    ⟨pre, tx, tail, l', htxs, hlen, hok, hfail⟩
  simp [htxs, hlen, List.length_append]

end Starstream.Oracle
