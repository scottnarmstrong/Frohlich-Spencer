/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.BasicLemmaRepaired
public import FroehlichSpencer.BKT.Charges.TorusDistance
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds
public import FroehlichSpencer.BKT.Charges.DensityBall
public import FroehlichSpencer.BKT.Charges.ScaleGeometry

/-! # Fine-cell packing count for the repaired Basic Lemma -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Shell distance of one of the ten fine-cell coordinates around a side-two
base square. -/
def basicLemmaCellShell (i : Fin 10) : Fin 5 := by
  by_cases h₁ : i.val < 4
  · exact ⟨4 - i.val, by omega⟩
  · by_cases h₂ : i.val < 6
    · exact ⟨0, by omega⟩
    · exact ⟨i.val - 5, by omega⟩

/-- The side bit distinguishes the two fine cells at each shell distance. -/
def basicLemmaCellSide (i : Fin 10) : Fin 2 := by
  by_cases h₁ : i.val < 4
  · exact ⟨0, by omega⟩
  · by_cases h₂ : i.val < 6
    · exact ⟨i.val - 4, by omega⟩
    · exact ⟨1, by omega⟩

theorem basicLemmaCellShellSide_injective (i j : Fin 10)
    (hμ : basicLemmaCellShell i = basicLemmaCellShell j)
    (hε : basicLemmaCellSide i = basicLemmaCellSide j) : i = j := by
  fin_cases i
  all_goals fin_cases j
  all_goals norm_num [basicLemmaCellShell, basicLemmaCellSide] at *

/-- The number of fine-cell steps separating a cell from the base square. -/
def basicLemmaCellGap (c : ℕ) (i : Fin 10) : ℕ :=
  if i.val < 4 then (3 - i.val) * c + 1
  else if i.val < 6 then 0
  else (i.val - 6) * c + 1

/-- The shell pairs permitted by an ℓ¹ reach of four fine-cell widths. -/
def basicLemmaReachableShellPairs : Finset (Fin 5 × Fin 5) :=
  Finset.univ.filter fun p => p.1.val = 0 ∨ p.2.val = 0 ∨ p.1.val + p.2.val ≤ 5

theorem basicLemmaReachableShellPairs_card : basicLemmaReachableShellPairs.card = 19 := by
  decide

private theorem basicLemmaCellGap_shell_bound (c : ℕ) (hc : 0 < c)
    (i j : Fin 10) (hgap : basicLemmaCellGap c i + basicLemmaCellGap c j ≤ 4 * c) :
    (basicLemmaCellShell i).val = 0 ∨ (basicLemmaCellShell j).val = 0 ∨
      (basicLemmaCellShell i).val + (basicLemmaCellShell j).val ≤ 5 := by
  fin_cases i <;> fin_cases j <;> first
    | decide
    | (norm_num [basicLemmaCellGap] at hgap; omega)

/-- The tile-count estimate: at most 76 fine cells meet the four-width
ℓ¹ enlargement of a side-two square. -/
theorem basicLemmaCellReachable_card_le (c : ℕ) (hc : 0 < c) :
    (Finset.univ.filter fun p : Fin 10 × Fin 10 =>
      basicLemmaCellGap c p.1 + basicLemmaCellGap c p.2 ≤ 4 * c).card ≤ 76 := by
  let I : Finset (Fin 10 × Fin 10) := Finset.univ.filter fun p =>
    basicLemmaCellGap c p.1 + basicLemmaCellGap c p.2 ≤ 4 * c
  let code : (Fin 10 × Fin 10) → (Fin 5 × Fin 5) × (Fin 2 × Fin 2) := fun p =>
    ((basicLemmaCellShell p.1, basicLemmaCellShell p.2),
      (basicLemmaCellSide p.1, basicLemmaCellSide p.2))
  have hcard : I.card ≤
      (basicLemmaReachableShellPairs ×ˢ (Finset.univ : Finset (Fin 2 × Fin 2))).card := by
    apply Finset.card_le_card_of_injOn code
    · intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hs := basicLemmaCellGap_shell_bound c hc p.1 p.2 hp'
      simp only [Finset.mem_coe, Finset.mem_product, code]
      exact ⟨by simpa [basicLemmaReachableShellPairs] using hs,
        Finset.mem_univ _⟩
    · intro p hp q hq hpq
      have hleft : (basicLemmaCellShell p.1, basicLemmaCellShell p.2) =
          (basicLemmaCellShell q.1, basicLemmaCellShell q.2) := congrArg Prod.fst hpq
      have hright : (basicLemmaCellSide p.1, basicLemmaCellSide p.2) =
          (basicLemmaCellSide q.1, basicLemmaCellSide q.2) := congrArg Prod.snd hpq
      have h₁ := basicLemmaCellShellSide_injective p.1 q.1
        (congrArg Prod.fst hleft) (congrArg Prod.fst hright)
      have h₂ := basicLemmaCellShellSide_injective p.2 q.2
        (congrArg Prod.snd hleft) (congrArg Prod.snd hright)
      exact Prod.ext h₁ h₂
  have htarget :
      (basicLemmaReachableShellPairs ×ˢ (Finset.univ : Finset (Fin 2 × Fin 2))).card = 76 := by
    simp [basicLemmaReachableShellPairs_card]
  simpa [I, htarget] using hcard

/-- Decompose one lifted coordinate near a side-`2c` square into one of the
ten side-`c` cells indexed by `Fin 10`. -/
theorem exists_basicLemmaCellCoordinates (c : ℕ) (hc : 0 < c) (z : ℤ)
    (hzlo : -(4 * (c : ℤ)) ≤ z) (hzhi : z < 6 * c) :
    ∃ i : Fin 10, ∃ u : Fin c,
      z = -(4 * (c : ℤ)) + (i.val : ℤ) * c + u.val := by
  let n := (z + 4 * (c : ℤ)).toNat
  have hn0 : 0 ≤ z + 4 * (c : ℤ) := by omega
  have hnlt : n < 10 * c := by
    dsimp [n]
    have hcast : ((z + 4 * (c : ℤ)).toNat : ℤ) = z + 4 * c :=
      Int.toNat_of_nonneg hn0
    have hnltZ : z + 4 * c < 10 * c := by omega
    exact_mod_cast (by omega : (n : ℤ) < 10 * c)
  have hi : n / c < 10 := (Nat.div_lt_iff_lt_mul hc).2 (by omega)
  have hu : n % c < c := Nat.mod_lt _ hc
  let i : Fin 10 := ⟨n / c, hi⟩
  let u : Fin c := ⟨n % c, hu⟩
  have hdecomp : n % c + c * (n / c) = n := Nat.mod_add_div n c
  have hdecompZ : ((n % c : ℕ) : ℤ) + ((c * (n / c) : ℕ) : ℤ) = (n : ℤ) := by
    exact_mod_cast hdecomp
  have hncast : (n : ℤ) = z + 4 * c := Int.toNat_of_nonneg hn0
  refine ⟨i, u, ?_⟩
  change z = -(4 * (c : ℤ)) + ((n / c : ℕ) : ℤ) * c + ((n % c : ℕ) : ℤ)
  calc
    z = n - 4 * c := by omega
    _ = ((n % c : ℕ) : ℤ) + ((c * (n / c) : ℕ) : ℤ) - 4 * c := by
      exact (congrArg (fun x : ℤ => x - 4 * c) hdecompZ).symm
    _ = -4 * c + ((n / c : ℕ) : ℤ) * c + ((n % c : ℕ) : ℤ) := by
      push_cast
      ring

/-- The lower corner of the fine cell indexed by `i`, relative to the base
square statement. -/
def basicLemmaCellStart {L : ℕ} (c : ℕ) (a : Fin L × Fin L) (i : Fin 10) : ℤ × ℤ :=
  ((a.1.val : ℤ) - 4 * c + (i.val : ℤ) * c,
    (a.2.val : ℤ) - 4 * c + (i.val : ℤ) * c)

/-- Clamp an integer lower endpoint to valid statement for a clipped cell. -/
def basicLemmaClampLower (L c : ℕ) (z : ℤ) : ℤ :=
  max 0 (min z ((L - c : ℕ) : ℤ))

/-- A clipped finite interval contains every in-domain point of its source
interval. -/
theorem basicLemmaClampLower_contains (L c : ℕ) (hc : c ≤ L) (z x : ℤ)
    (hx0 : 0 ≤ x) (hxL : x < L) (hleft : z ≤ x)
    (hright : x ≤ z + (c : ℤ) - 1) :
    basicLemmaClampLower L c z ≤ x ∧ x ≤ basicLemmaClampLower L c z + c - 1 := by
  have hu0 : 0 ≤ ((L - c : ℕ) : ℤ) := by omega
  by_cases hz0 : z ≤ 0
  · simp [basicLemmaClampLower, min_eq_left (le_trans hz0 hu0), max_eq_left hz0]
    omega
  · have hzpos : 0 < z := by omega
    by_cases hzu : z ≤ ((L - c : ℕ) : ℤ)
    · simp [basicLemmaClampLower, min_eq_left hzu,
        max_eq_right (le_of_lt hzpos)]
      omega
    · have huz : ((L - c : ℕ) : ℤ) < z := by omega
      simp [basicLemmaClampLower, min_eq_right (le_of_lt huz)]
      have hxUpper : x ≤ (L : ℤ) - 1 := by omega
      omega

/-- The clamped lower endpoint as a `Fin L` statement. -/
noncomputable def basicLemmaClampFin (L c : ℕ) (hc : 0 < c)
    (hclt : c < L) (z : ℤ) : Fin L := by
  let u := basicLemmaClampLower L c z
  have hu0 : 0 ≤ u := le_max_left _ _
  have huUpper : u ≤ ((L - c : ℕ) : ℤ) := by
    dsimp [u, basicLemmaClampLower]
    exact max_le (by omega) (min_le_right _ _)
  have huLt : u < L := by omega
  have huNatLt : u.toNat < L := by
    have hcast : (u.toNat : ℤ) < L := by
      rw [Int.toNat_of_nonneg hu0]
      exact huLt
    exact_mod_cast hcast
  exact ⟨u.toNat, huNatLt⟩

/-- Cast form of the clamped statement coordinate. -/
theorem basicLemmaClampFin_cast (L c : ℕ) (hc : 0 < c)
    (hclt : c < L) (z : ℤ) :
    ((basicLemmaClampFin L c hc hclt z).val : ℤ) = basicLemmaClampLower L c z := by
  unfold basicLemmaClampFin
  dsimp
  exact Int.toNat_of_nonneg (le_max_left _ _)

/-- The clipped statement for a lifted free cell. -/
noncomputable def basicLemmaFreeCellAnchor (L c : ℕ) (hc : 0 < c)
    (hclt : c < L) (p : LiftedPoint) : Fin L × Fin L :=
  (basicLemmaClampFin L c hc hclt p.1, basicLemmaClampFin L c hc hclt p.2)

/-- Every in-domain point of a lifted square is in its clamped free cell. -/
theorem basicLemmaFreePoint_mem_clampedCell (L K : ℕ) (hK : squareSide K < L)
    (p : LiftedPoint) (z : Fin L × Fin L)
    (hz : ((z.1.val : ℤ), (z.2.val : ℤ)) ∈ liftedSquare (squareSide K) p) :
    z ∈ kpSquare .free L K (basicLemmaFreeCellAnchor L (squareSide K)
      (by unfold squareSide; exact Nat.pow_pos (by decide)) hK p) := by
  have hx : p.1 ≤ z.1.val ∧ z.1.val ≤ p.1 + (squareSide K : ℤ) - 1 ∧
      p.2 ≤ z.2.val ∧ z.2.val ≤ p.2 + (squareSide K : ℤ) - 1 := hz
  have hx₁ := basicLemmaClampLower_contains L (squareSide K) (le_of_lt hK)
    p.1 z.1.val (by positivity) (by exact_mod_cast z.1.isLt) hx.1 hx.2.1
  have hx₂ := basicLemmaClampLower_contains L (squareSide K) (le_of_lt hK)
    p.2 z.2.val (by positivity) (by exact_mod_cast z.2.isLt) hx.2.2.1 hx.2.2.2
  have hside : squareSide K ≤ L := le_of_lt hK
  have hKpos : 0 < squareSide K := by
    unfold squareSide
    exact Nat.pow_pos (by decide)
  have hcast₁ : ((basicLemmaFreeCellAnchor L (squareSide K)
      hKpos hK p).1.val : ℤ) = basicLemmaClampLower L (squareSide K) p.1 := by
    simp only [basicLemmaFreeCellAnchor]
    exact basicLemmaClampFin_cast L (squareSide K) hKpos hK p.1
  have hcast₂ : ((basicLemmaFreeCellAnchor L (squareSide K)
      hKpos hK p).2.val : ℤ) = basicLemmaClampLower L (squareSide K) p.2 := by
    simp only [basicLemmaFreeCellAnchor]
    exact basicLemmaClampFin_cast L (squareSide K) hKpos hK p.2
  rw [mem_kpSquare_free_iff L K hside]
  constructor
  · have hcast : ((basicLemmaFreeCellAnchor L (squareSide K)
        (Nat.pow_pos (by decide)) hK p).1.val : ℤ) ≤ z.1.val := by
      rw [hcast₁]
      exact hx₁.1
    exact_mod_cast hcast
  · constructor
    · have hcast : (z.1.val : ℤ) <
          ((basicLemmaFreeCellAnchor L (squareSide K)
            hKpos hK p).1.val : ℤ) + squareSide K := by
        rw [hcast₁]
        omega
      exact_mod_cast hcast
    · constructor
      · have hcast : ((basicLemmaFreeCellAnchor L (squareSide K)
            (Nat.pow_pos (by decide)) hK p).2.val : ℤ) ≤ z.2.val := by
          rw [hcast₂]
          exact hx₂.1
        exact_mod_cast hcast
      · have hcast : (z.2.val : ℤ) <
          ((basicLemmaFreeCellAnchor L (squareSide K)
            hKpos hK p).2.val : ℤ) + squareSide K := by
          rw [hcast₂]
          omega
        exact_mod_cast hcast

/-- One wrapped or clipped fine cell, represented by an allowed scale square. -/
noncomputable def basicLemmaFineCell (boundary : SquareBoundary) (L K : ℕ)
  (hL : 1 < L) (hbase : 2 * squareSide K ≤ L)
    (a : Fin L × Fin L) (i j : Fin 10) : Finset (Fin L × Fin L) := by
  let c := squareSide K
  let start : LiftedPoint :=
    ((basicLemmaCellStart c a i).1, (basicLemmaCellStart c a j).2)
  cases boundary with
  | free =>
      have hcell : squareSide K < L := by
        have hc : 0 < squareSide K := Nat.pow_pos (by decide)
        omega
      exact kpSquare .free L K (basicLemmaFreeCellAnchor L (squareSide K)
        (by unfold squareSide; exact Nat.pow_pos (by decide)) hcell start)
  | periodic =>
      exact kpSquare .periodic L K
        (periodicProjection L (by omega) start)

/-- The finite family of fine cells at graph distance at most `2^k` from the
base square anchored at `a`; the shell count has already bounded its size. -/
noncomputable def basicLemmaCellsForSquare (boundary : SquareBoundary) (L K : ℕ)
    (hL : 1 < L) (hbase : 2 * squareSide K ≤ L) (a : Fin L × Fin L) :
    Finset (Finset (Fin L × Fin L)) :=
  (Finset.univ.filter fun p : Fin 10 × Fin 10 =>
    basicLemmaCellGap (squareSide K) p.1 + basicLemmaCellGap (squareSide K) p.2 ≤
      4 * squareSide K).image fun p => basicLemmaFineCell boundary L K hL hbase a p.1 p.2

theorem basicLemmaCellsForSquare_card_le (boundary : SquareBoundary) (L K : ℕ)
    (hL : 1 < L) (hbase : 2 * squareSide K ≤ L) (a : Fin L × Fin L) :
    (basicLemmaCellsForSquare boundary L K hL hbase a).card ≤ 76 := by
  unfold basicLemmaCellsForSquare
  calc
    _ ≤ (Finset.univ.filter fun p : Fin 10 × Fin 10 =>
        basicLemmaCellGap (squareSide K) p.1 + basicLemmaCellGap (squareSide K) p.2 ≤
          4 * squareSide K).card := Finset.card_image_le
    _ ≤ 76 := basicLemmaCellReachable_card_le _ (Nat.pow_pos (by decide))

/-- The shell gap in one coordinate is bounded by the displacement from any
point of that fine cell to any point of the base square. -/
theorem basicLemmaCellGap_le_abs (c : ℕ) (i : Fin 10)
    (u : Fin c) (v : Fin (2 * c)) :
    (basicLemmaCellGap c i : ℤ) ≤
      |-(4 * (c : ℤ)) + (i.val : ℤ) * c + u.val - v.val| := by
  have hu0 : 0 ≤ (u.val : ℤ) := by positivity
  have huc : (u.val : ℤ) < c := by exact_mod_cast u.isLt
  have hv0 : 0 ≤ (v.val : ℤ) := by positivity
  have hvc : (v.val : ℤ) < 2 * c := by exact_mod_cast v.isLt
  let z : ℤ := -(4 * (c : ℤ)) + (i.val : ℤ) * c + u.val
  by_cases hnonneg : 0 ≤ z - v.val
  · rw [abs_of_nonneg hnonneg]
    subst z
    fin_cases i
    all_goals norm_num [basicLemmaCellGap] at hnonneg ⊢
    all_goals omega
  · have hneg : z - v.val < 0 := by omega
    rw [abs_of_neg hneg]
    subst z
    fin_cases i
    all_goals norm_num [basicLemmaCellGap] at hnonneg ⊢
    all_goals omega

/-- The coordinate ℓ¹ distance on the free square. -/
def basicLemmaFreeL1 {L : ℕ} (x y : Fin L × Fin L) : ℤ :=
  |(y.1.val : ℤ) - x.1.val| + |(y.2.val : ℤ) - x.2.val|

private theorem basicLemmaSquareFreeEdgeL1 {L : ℕ} (e : SquareFreeEdge L) :
    |(e.1.1.1.val : ℤ) - e.1.2.1.val| +
      |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 1 := by
  have hshape :
      ({|(e.1.1.1.val : ℤ) - e.1.2.1.val|,
        |(e.1.1.2.val : ℤ) - e.1.2.2.val|} : Finset ℤ) =
          ({0, 1} : Finset ℤ) := by
    simpa using e.property.2
  have hx : |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈
      ({0, 1} : Finset ℤ) := by
    have heq := congrArg (fun s : Finset ℤ =>
      |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈ s) hshape
    have hmem : |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈
        ({|(e.1.1.1.val : ℤ) - e.1.2.1.val|,
          |(e.1.1.2.val : ℤ) - e.1.2.2.val|} : Finset ℤ) := by simp
    exact heq.mp hmem
  have hy : |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈
      ({0, 1} : Finset ℤ) := by
    have heq := congrArg (fun s : Finset ℤ =>
      |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈ s) hshape
    have hmem : |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈
        ({|(e.1.1.1.val : ℤ) - e.1.2.1.val|,
          |(e.1.1.2.val : ℤ) - e.1.2.2.val|} : Finset ℤ) := by simp
    exact heq.mp hmem
  have hne : |(e.1.1.1.val : ℤ) - e.1.2.1.val| ≠
      |(e.1.1.2.val : ℤ) - e.1.2.2.val| := by
    intro heq
    have hcard := congrArg Finset.card hshape
    simp [heq] at hcard
  rcases Finset.mem_insert.mp hx with hx | hx
  · rcases Finset.mem_insert.mp hy with hy | hy
    · have hx0 : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 0 := hx
      have hy0 : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 0 := by simpa using hy
      exact (hne (by rw [hx0, hy0])).elim
    · have hx0 : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 0 := hx
      have hy1 : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 1 := by simpa using hy
      simp [hx0, hy1]
  · rcases Finset.mem_insert.mp hy with hy | hy
    · have hx1 : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 1 := by simpa using hx
      have hy0 : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 0 := hy
      simp [hx1, hy0]
    · have hx1 : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 1 := by simpa using hx
      have hy1 : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 1 := by simpa using hy
      exact (hne (by rw [hx1, hy1])).elim

private theorem basicLemmaFreeEdgeL1 {L : ℕ} {x y : Fin L × Fin L}
    (hxy : (squareFree L).toSimpleGraph.Adj x y) :
    basicLemmaFreeL1 x y = 1 := by
  obtain ⟨hne, ⟨e, hedge | hedge⟩⟩ := (freeAdj_iff_edgeRelation L x y).mp hxy
  · rcases hedge with ⟨he₁, he₂⟩
    have h := basicLemmaSquareFreeEdgeL1 e
    rw [he₁, he₂] at h
    simpa [basicLemmaFreeL1, abs_sub_comm, add_comm] using h
  · rcases hedge with ⟨he₁, he₂⟩
    have h := basicLemmaSquareFreeEdgeL1 e
    rw [he₁, he₂] at h
    simpa [basicLemmaFreeL1, abs_sub_comm, add_comm] using h

private theorem basicLemmaFreeWalkL1 {L : ℕ} {x y : Fin L × Fin L}
    (w : (squareFree L).toSimpleGraph.Walk x y) :
    basicLemmaFreeL1 x y ≤ w.length := by
  induction w with
  | nil => simp [basicLemmaFreeL1]
  | @cons a b c habc tail ih =>
      have h₁ : |(c.1.val : ℤ) - a.1.val| ≤
          |(b.1.val : ℤ) - a.1.val| + |(c.1.val : ℤ) - b.1.val| := by
        calc
          |(c.1.val : ℤ) - a.1.val| =
              |((c.1.val : ℤ) - b.1.val) + ((b.1.val : ℤ) - a.1.val)| := by
                congr 1
                ring
          _ ≤ |(c.1.val : ℤ) - b.1.val| + |(b.1.val : ℤ) - a.1.val| := by
            calc
              |((c.1.val : ℤ) - b.1.val) + ((b.1.val : ℤ) - a.1.val)| =
                  |(c.1.val : ℤ) - a.1.val| := by
                congr 1
                ring
              _ ≤ _ := abs_sub_le (c.1.val : ℤ) (b.1.val : ℤ) (a.1.val : ℤ)
          _ = _ := by ring
      have h₂ : |(c.2.val : ℤ) - a.2.val| ≤
          |(b.2.val : ℤ) - a.2.val| + |(c.2.val : ℤ) - b.2.val| := by
        calc
          |(c.2.val : ℤ) - a.2.val| =
              |((c.2.val : ℤ) - b.2.val) + ((b.2.val : ℤ) - a.2.val)| := by
                congr 1
                ring
          _ ≤ |(c.2.val : ℤ) - b.2.val| + |(b.2.val : ℤ) - a.2.val| := by
            calc
              |((c.2.val : ℤ) - b.2.val) + ((b.2.val : ℤ) - a.2.val)| =
                  |(c.2.val : ℤ) - a.2.val| := by
                congr 1
                ring
              _ ≤ _ := abs_sub_le (c.2.val : ℤ) (b.2.val : ℤ) (a.2.val : ℤ)
          _ = _ := by ring
      have hedge := basicLemmaFreeEdgeL1 habc
      have htail := ih
      simp only [SimpleGraph.Walk.length_cons] at htail ⊢
      simp only [basicLemmaFreeL1] at hedge htail ⊢
      omega

theorem basicLemmaFreeDistance_l1_le (L : ℕ) (hL : 1 < L)
    (x y : Fin L × Fin L) :
    basicLemmaFreeL1 x y ≤ (latticeDistance .free L x y : ℤ) := by
  have hconn : (squareFree L).toSimpleGraph.Connected := squareFree_connected L hL
  obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist x y
  have hwalk := basicLemmaFreeWalkL1 w
  have hw' : w.length = latticeDistance .free L x y := by
    simpa [latticeDistance] using hw
  exact_mod_cast (hw' ▸ hwalk)

private def basicLemmaDiamondOne : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-1 : ℤ) 1) ×ˢ (Finset.Icc (-1 : ℤ) 1)).filter
    fun p => |p.1| + |p.2| ≤ 1

private def basicLemmaDiamondTwo : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2)).filter
    fun p => |p.1| + |p.2| ≤ 2

private theorem basicLemmaDiamondOne_card : basicLemmaDiamondOne.card = 5 := by
  decide

private theorem basicLemmaDiamondTwo_card : basicLemmaDiamondTwo.card = 13 := by
  decide

private theorem basicLemmaFreeBall_card_le_diamond (L : ℕ) (hL : 1 < L)
    (j : Fin L × Fin L) (R : ℕ) (hRlo : 1 ≤ R) (hR : R ≤ 2)
    (D : Finset (ℤ × ℤ)) (hD : D = if R = 1 then basicLemmaDiamondOne else
      basicLemmaDiamondTwo) :
    (Finset.univ.filter fun x : Fin L × Fin L =>
      latticeDistance .free L x j ≤ R).card ≤ D.card := by
  classical
  let B := Finset.univ.filter fun x : Fin L × Fin L => latticeDistance .free L x j ≤ R
  let f : (Fin L × Fin L) → (ℤ × ℤ) := fun x =>
    ((x.1.val : ℤ) - j.1.val, (x.2.val : ℤ) - j.2.val)
  change B.card ≤ D.card
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    have hx := (Finset.mem_filter.mp hx).2
    have hdist := basicLemmaFreeDistance_l1_le L hL j x
    have hsymm : latticeDistance .free L j x = latticeDistance .free L x j := by
      change (squareFree L).toSimpleGraph.dist j x =
        (squareFree L).toSimpleGraph.dist x j
      exact SimpleGraph.dist_comm
    have hdistR : latticeDistance .free L j x ≤ R := by
      rw [hsymm]
      exact hx
    have hdistRZ : (latticeDistance .free L j x : ℤ) ≤ R := by exact_mod_cast hdistR
    have hxy : basicLemmaFreeL1 j x ≤ R := hdist.trans hdistRZ
    have hmem : f x ∈ (if R = 1 then basicLemmaDiamondOne else basicLemmaDiamondTwo) := by
      by_cases hR1 : R = 1
      · simp only [hR1, ite_true]
        change f x ∈ ((Finset.Icc (-1 : ℤ) 1) ×ˢ (Finset.Icc (-1 : ℤ) 1)).filter _
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, f]
        simp only [basicLemmaFreeL1] at hxy
        rw [hR1] at hxy
        have hx1 := abs_le.mp (show |(x.1.val : ℤ) - j.1.val| ≤ 1 by
          have hnonneg : 0 ≤ |(x.2.val : ℤ) - j.2.val| := abs_nonneg _
          omega)
        have hx2 := abs_le.mp (show |(x.2.val : ℤ) - j.2.val| ≤ 1 by
          have hnonneg : 0 ≤ |(x.1.val : ℤ) - j.1.val| := abs_nonneg _
          omega)
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      · have hR2 : R = 2 := by omega
        simp only [hR1, ite_false]
        change f x ∈ ((Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2)).filter _
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, f]
        simp only [basicLemmaFreeL1] at hxy
        rw [hR2] at hxy
        have hx1 := abs_le.mp (show |(x.1.val : ℤ) - j.1.val| ≤ 2 by
          have hnonneg : 0 ≤ |(x.2.val : ℤ) - j.2.val| := abs_nonneg _
          omega)
        have hx2 := abs_le.mp (show |(x.2.val : ℤ) - j.2.val| ≤ 2 by
          have hnonneg : 0 ≤ |(x.1.val : ℤ) - j.1.val| := abs_nonneg _
          omega)
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [hD]
    exact hmem
  · intro x hx y hy hxy
    have hxy' : f x = f y := hxy
    simp only [f, Prod.mk.injEq] at hxy'
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

private theorem basicLemmaPeriodicBall_card_le_diamond (L : ℕ)
    (j : Fin L × Fin L) (R : ℕ) (hRlo : 1 ≤ R) (hR : R ≤ 2)
    (D : Finset (ℤ × ℤ)) (hD : D = if R = 1 then basicLemmaDiamondOne else
      basicLemmaDiamondTwo) :
    (Finset.univ.filter fun x : Fin L × Fin L =>
      latticeDistance .periodic L x j ≤ R).card ≤ D.card := by
  classical
  let hL : 0 < L := Fin.pos j.1
  let p : LiftedPoint := ((j.1.val : ℤ), (j.2.val : ℤ))
  have hp : periodicProjection L hL p = j := periodicProjection_val L hL j
  choose q hq hd using fun x : Fin L × Fin L =>
    exists_lift_liftedL1_eq_dist L hL j x p hp
  let f : (Fin L × Fin L) → (ℤ × ℤ) := fun x =>
    ((q x).1 - p.1, (q x).2 - p.2)
  let B := Finset.univ.filter fun x : Fin L × Fin L => latticeDistance .periodic L x j ≤ R
  change B.card ≤ D.card
  apply Finset.card_le_card_of_injOn f
  · intro x hx
    have hx := (Finset.mem_filter.mp hx).2
    have hdist : latticeDistance .periodic L j x = latticeDistance .periodic L x j := by
      change (squarePeriodic L).toSimpleGraph.dist j x =
        (squarePeriodic L).toSimpleGraph.dist x j
      exact SimpleGraph.dist_comm
    have hdistR : latticeDistance .periodic L j x ≤ R := by
      rw [hdist]
      exact hx
    have hsmall : liftedL1 p (q x) ≤ R := by
      rw [hd x]
      exact_mod_cast hdistR
    have hmem : f x ∈ (if R = 1 then basicLemmaDiamondOne else basicLemmaDiamondTwo) := by
      by_cases hR1 : R = 1
      · simp only [hR1, ite_true]
        change f x ∈ ((Finset.Icc (-1 : ℤ) 1) ×ˢ (Finset.Icc (-1 : ℤ) 1)).filter _
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, f]
        simp only [liftedL1] at hsmall
        rw [hR1] at hsmall
        have hx1 := abs_le.mp (show |(q x).1 - p.1| ≤ 1 by
          have hnonneg : 0 ≤ |(q x).2 - p.2| := abs_nonneg _
          omega)
        have hx2 := abs_le.mp (show |(q x).2 - p.2| ≤ 1 by
          have hnonneg : 0 ≤ |(q x).1 - p.1| := abs_nonneg _
          omega)
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      · have hR2 : R = 2 := by omega
        simp only [hR1, ite_false]
        change f x ∈ ((Finset.Icc (-2 : ℤ) 2) ×ˢ (Finset.Icc (-2 : ℤ) 2)).filter _
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, f]
        simp only [liftedL1] at hsmall
        rw [hR2] at hsmall
        have hx1 := abs_le.mp (show |(q x).1 - p.1| ≤ 2 by
          have hnonneg : 0 ≤ |(q x).2 - p.2| := abs_nonneg _
          omega)
        have hx2 := abs_le.mp (show |(q x).2 - p.2| ≤ 2 by
          have hnonneg : 0 ≤ |(q x).1 - p.1| := abs_nonneg _
          omega)
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    rw [hD]
    exact hmem
  · intro x hx y hy hxy
    have hxy' : f x = f y := hxy
    simp only [f, Prod.mk.injEq] at hxy'
    have hxmod := periodicProjection_modEq L hL (hq x)
    have hymod := periodicProjection_modEq L hL (hq y)
    have h₁ : (x.1.val : ℤ) ≡ y.1.val [ZMOD L] := by
      have heq : (q x).1 = (q y).1 := by omega
      calc
        (x.1.val : ℤ) ≡ (q x).1 [ZMOD L] := hxmod.1.symm
        _ = (q y).1 := heq
        _ ≡ y.1.val [ZMOD L] := hymod.1
    have h₂ : (x.2.val : ℤ) ≡ y.2.val [ZMOD L] := by
      have heq : (q x).2 = (q y).2 := by omega
      calc
        (x.2.val : ℤ) ≡ (q x).2 [ZMOD L] := hxmod.2.symm
        _ = (q y).2 := heq
        _ ≡ y.2.val [ZMOD L] := hymod.2
    exact Prod.ext (fin_eq_of_val_modEq h₁) (fin_eq_of_val_modEq h₂)

theorem basicLemmaBall_radius_one_card_le (boundary : SquareBoundary) (L : ℕ)
    (j : Fin L × Fin L) :
    (Finset.univ.filter fun x : Fin L × Fin L =>
      latticeDistance boundary L x j ≤ 1).card ≤ 5 := by
  cases boundary with
  | free =>
      by_cases hL : 1 < L
      · have h := basicLemmaFreeBall_card_le_diamond L hL j 1 (by omega) (by omega)
          basicLemmaDiamondOne rfl
        simpa [basicLemmaDiamondOne_card] using h
      · have hcard : (Finset.univ.filter fun x : Fin L × Fin L =>
            latticeDistance .free L x j ≤ 1).card ≤ 1 := by
          have hL1 : L = 1 := by have hp := Fin.pos j.1; omega
          calc
            _ ≤ Fintype.card (Fin L × Fin L) := Finset.card_le_univ _
            _ = L * L := by simp
            _ = 1 := by simp [hL1]
        omega
  | periodic =>
      have h := basicLemmaPeriodicBall_card_le_diamond L j 1 (by omega) (by omega)
        basicLemmaDiamondOne rfl
      simpa [basicLemmaDiamondOne_card] using h

theorem basicLemmaBall_radius_two_card_le (boundary : SquareBoundary) (L : ℕ)
    (j : Fin L × Fin L) :
    (Finset.univ.filter fun x : Fin L × Fin L =>
      latticeDistance boundary L x j ≤ 2).card ≤ 13 := by
  cases boundary with
  | free =>
      by_cases hL : 1 < L
      · have h := basicLemmaFreeBall_card_le_diamond L hL j 2 (by omega) (by omega)
          basicLemmaDiamondTwo rfl
        simpa [basicLemmaDiamondTwo_card] using h
      · have hcard : (Finset.univ.filter fun x : Fin L × Fin L =>
            latticeDistance .free L x j ≤ 2).card ≤ 1 := by
          have hL1 : L = 1 := by have hp := Fin.pos j.1; omega
          calc
            _ ≤ Fintype.card (Fin L × Fin L) := Finset.card_le_univ _
            _ = L * L := by simp
            _ = 1 := by simp [hL1]
        omega
  | periodic =>
      have h := basicLemmaPeriodicBall_card_le_diamond L j 2 (by omega) (by omega)
        basicLemmaDiamondTwo rfl
      simpa [basicLemmaDiamondTwo_card] using h

private theorem squareSide_prevprev_succ (k : ℕ) (hk : 2 ≤ k) :
    squareSide (k - 1) = 2 * squareSide (k - 2) := by
  have h₁ : k - 1 = (k - 2) + 1 := by omega
  unfold squareSide
  rw [h₁, pow_succ]
  exact Nat.mul_comm _ _

private theorem squareSide_prevprev_rad (k : ℕ) (hk : 2 ≤ k) :
    2 ^ k = 4 * squareSide (k - 2) := by
  have hs := squareSide_prevprev_succ k hk
  have h₂ : k = (k - 1) + 1 := by omega
  have hs' : 2 ^ (k - 1) = 2 * squareSide (k - 2) := by simpa [squareSide] using hs
  calc
    2 ^ k = 2 ^ ((k - 1) + 1) := congrArg (fun n : ℕ => 2 ^ n) h₂
    _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
    _ = (2 * squareSide (k - 2)) * 2 := by rw [hs']
    _ = 4 * squareSide (k - 2) := by ring

theorem basicLemmaFineCell_diameter_le (boundary : SquareBoundary) (L K : ℕ)
    (hL : 1 < L) (hbase : 2 * squareSide K ≤ L)
    (a : Fin L × Fin L) (i j : Fin 10) :
    squareDiameter boundary L (basicLemmaFineCell boundary L K hL hbase a i j) ≤
      2 * (squareSide K - 1) := by
  have hmem : basicLemmaFineCell boundary L K hL hbase a i j ∈ kpSquares boundary L K := by
    cases boundary with
    | free =>
        let hK : 0 < squareSide K := Nat.pow_pos (by decide)
        have hLt : squareSide K < L := by omega
        simp [basicLemmaFineCell, kpSquares]
    | periodic =>
        simp [basicLemmaFineCell, kpSquares]
  cases boundary with
  | free =>
      have hside : squareSide K ≤ L := by omega
      simpa [basicLemmaFineCell] using
        free_squareDiameter_le L K _ hmem hside
  | periodic =>
      simpa [basicLemmaFineCell] using
        periodic_squareDiameter_le L K hL _ hmem

theorem basicLemmaFreeFineCell_covering (L k : ℕ) (hk : 2 ≤ k)
    (hL : 1 < L) (hbase : 2 * squareSide (k - 2) ≤ L)
    (a x y : Fin L × Fin L)
    (hy : y ∈ kpSquare .free L (k - 1) a)
    (hd : latticeDistance .free L x y ≤ 2 ^ k) :
    ∃ i j : Fin 10,
      basicLemmaCellGap (squareSide (k - 2)) i +
          basicLemmaCellGap (squareSide (k - 2)) j ≤ 4 * squareSide (k - 2) ∧
        x ∈ basicLemmaFineCell .free L (k - 2) hL hbase a i j := by
  let c := squareSide (k - 2)
  have hc : 0 < c := by dsimp [c, squareSide]; positivity
  have hside := squareSide_prevprev_succ k hk
  have hrad := squareSide_prevprev_rad k hk
  have hfits : squareSide (k - 1) ≤ L := by rw [hside]; omega
  have hy' := (mem_kpSquare_free_iff L (k - 1) hfits a y).1 hy
  have hdist := basicLemmaFreeDistance_l1_le L hL y x
  have hdistR : (latticeDistance .free L y x : ℤ) ≤ 4 * (c : ℤ) := by
    have hcomm : latticeDistance .free L y x = latticeDistance .free L x y := by
      change (squareFree L).toSimpleGraph.dist y x =
        (squareFree L).toSimpleGraph.dist x y
      exact SimpleGraph.dist_comm
    have hdNat : latticeDistance .free L y x ≤ 4 * c := by
      calc
        latticeDistance .free L y x = latticeDistance .free L x y := hcomm
        _ ≤ 2 ^ k := hd
        _ = 4 * c := by simpa [c] using hrad
    exact_mod_cast hdNat
  have hdx : |(x.1.val : ℤ) - y.1.val| ≤ 4 * (c : ℤ) := by
    unfold basicLemmaFreeL1 at hdist
    have hnonneg : 0 ≤ |(x.2.val : ℤ) - y.2.val| := abs_nonneg _
    omega
  have hdy : |(x.2.val : ℤ) - y.2.val| ≤ 4 * (c : ℤ) := by
    unfold basicLemmaFreeL1 at hdist
    have hnonneg : 0 ≤ |(x.1.val : ℤ) - y.1.val| := abs_nonneg _
    omega
  let zx : ℤ := (x.1.val : ℤ) - a.1.val
  let zy : ℤ := (x.2.val : ℤ) - a.2.val
  have hzxl : -(4 * (c : ℤ)) ≤ zx := by
    have hdx' := abs_le.mp hdx
    dsimp [zx]
    omega
  have hzxu : zx < 6 * (c : ℤ) := by
    have hdx' := abs_le.mp hdx
    dsimp [zx]
    omega
  have hzyL : -(4 * (c : ℤ)) ≤ zy := by
    have hdy' := abs_le.mp hdy
    dsimp [zy]
    omega
  have hzyu : zy < 6 * (c : ℤ) := by
    have hdy' := abs_le.mp hdy
    dsimp [zy]
    omega
  obtain ⟨i, u, hux⟩ := exists_basicLemmaCellCoordinates c hc zx hzxl hzxu
  obtain ⟨j, v, hvy⟩ := exists_basicLemmaCellCoordinates c hc zy hzyL hzyu
  let vx : Fin (2 * c) := ⟨y.1.val - a.1.val, by omega⟩
  let vy : Fin (2 * c) := ⟨y.2.val - a.2.val, by omega⟩
  have hvx : (vx.val : ℤ) = (y.1.val : ℤ) - a.1.val := by
    dsimp [vx]
    omega
  have hvy' : (vy.val : ℤ) = (y.2.val : ℤ) - a.2.val := by
    dsimp [vy]
    omega
  have hgapx := basicLemmaCellGap_le_abs c i u vx
  have hgapy := basicLemmaCellGap_le_abs c j v vy
  have hrelx : -(4 * (c : ℤ)) + (i.val : ℤ) * c + u.val - vx.val =
      (x.1.val : ℤ) - y.1.val := by
    dsimp [zx] at hux
    rw [← hux, hvx]
    ring
  have hrely : -(4 * (c : ℤ)) + (j.val : ℤ) * c + v.val - vy.val =
      (x.2.val : ℤ) - y.2.val := by
    dsimp [zy] at hvy
    rw [← hvy, hvy']
    ring
  rw [hrelx] at hgapx
  rw [hrely] at hgapy
  have hgap :
      (basicLemmaCellGap c i + basicLemmaCellGap c j : ℤ) ≤ 4 * (c : ℤ) := by
    calc
      _ ≤ |(x.1.val : ℤ) - y.1.val| + |(x.2.val : ℤ) - y.2.val| := add_le_add hgapx hgapy
      _ = basicLemmaFreeL1 y x := rfl
      _ ≤ (latticeDistance .free L y x : ℤ) := hdist
      _ ≤ 4 * (c : ℤ) := hdistR
  have hgapNat : basicLemmaCellGap c i + basicLemmaCellGap c j ≤ 4 * c := by
    exact_mod_cast hgap
  let p : LiftedPoint := ((a.1.val : ℤ) - 4 * c + (i.val : ℤ) * c,
    (a.2.val : ℤ) - 4 * c + (j.val : ℤ) * c)
  have hbox : ((x.1.val : ℤ), (x.2.val : ℤ)) ∈ liftedSquare c p := by
    change p.1 ≤ x.1.val ∧ x.1.val ≤ p.1 + (c : ℤ) - 1 ∧
      p.2 ≤ x.2.val ∧ x.2.val ≤ p.2 + (c : ℤ) - 1
    have hu0 : 0 ≤ (u.val : ℤ) := by positivity
    have hv0 : 0 ≤ (v.val : ℤ) := by positivity
    have huc : (u.val : ℤ) < c := by exact_mod_cast u.isLt
    have hvc : (v.val : ℤ) < c := by exact_mod_cast v.isLt
    have hux' := hux
    have hvy'' := hvy
    dsimp [zx] at hux'
    dsimp [zy] at hvy''
    dsimp [p]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  have hKlt : squareSide (k - 2) < L := by
    have hpos : 0 < squareSide (k - 2) := Nat.pow_pos (by decide)
    omega
  have hcell := basicLemmaFreePoint_mem_clampedCell L (k - 2) hKlt p x hbox
  refine ⟨i, j, hgapNat, ?_⟩
  simpa [basicLemmaFineCell, basicLemmaCellStart, c, p] using hcell

theorem basicLemmaPeriodicFineCell_covering (L k : ℕ) (hk : 2 ≤ k)
    (hL : 1 < L) (hbase : 2 * squareSide (k - 2) < L)
    (a x y : Fin L × Fin L)
    (hy : y ∈ kpSquare .periodic L (k - 1) a)
    (hd : latticeDistance .periodic L x y ≤ 2 ^ k) :
    ∃ i j : Fin 10,
      basicLemmaCellGap (squareSide (k - 2)) i +
          basicLemmaCellGap (squareSide (k - 2)) j ≤ 4 * squareSide (k - 2) ∧
        x ∈ basicLemmaFineCell .periodic L (k - 2) hL
          (by omega) a i j := by
  let c := squareSide (k - 2)
  have hc : 0 < c := by dsimp [c, squareSide]; positivity
  have hside := squareSide_prevprev_succ k hk
  have hrad := squareSide_prevprev_rad k hk
  have hfits : squareSide (k - 1) < L := by rw [hside]; simpa [c] using hbase
  have hmem := (mem_kpSquare_periodic_iff L (k - 1) hfits a y).1 hy
  obtain ⟨uBase, huBase, vBase, hvBase, hcoords⟩ := hmem
  let hLpos : 0 < L := by omega
  let baseLift : LiftedPoint :=
    (((a.1.val + uBase : ℕ) : ℤ), ((a.2.val + vBase : ℕ) : ℤ))
  have hbaseProj : periodicProjection L hLpos baseLift = y := by
    apply Prod.ext <;> apply Fin.ext
    · change (periodicCoordinate L hLpos ((a.1.val + uBase : ℕ) : ℤ)).val = y.1.val
      have hsum : ((a.1.val + uBase : ℕ) : ℤ) =
          (a.1.val : ℤ) + (uBase : ℤ) := by norm_cast
      rw [hsum, periodicCoordinate_add_nat, periodicCoordinate_finVal]
      exact hcoords.1.symm
    · change (periodicCoordinate L hLpos ((a.2.val + vBase : ℕ) : ℤ)).val = y.2.val
      have hsum : ((a.2.val + vBase : ℕ) : ℤ) =
          (a.2.val : ℤ) + (vBase : ℤ) := by norm_cast
      rw [hsum, periodicCoordinate_add_nat, periodicCoordinate_finVal]
      exact hcoords.2.symm
  obtain ⟨xLift, hxProj, hdistLift⟩ :=
    exists_lift_liftedL1_eq_dist L hLpos y x baseLift hbaseProj
  have hcomm : latticeDistance .periodic L y x = latticeDistance .periodic L x y := by
    change (squarePeriodic L).toSimpleGraph.dist y x =
      (squarePeriodic L).toSimpleGraph.dist x y
    exact SimpleGraph.dist_comm
  have hdistZ : (latticeDistance .periodic L y x : ℤ) ≤ 4 * (c : ℤ) := by
    have hnat : latticeDistance .periodic L y x ≤ 4 * c := by
      calc
        latticeDistance .periodic L y x = latticeDistance .periodic L x y := hcomm
        _ ≤ 2 ^ k := hd
        _ = 4 * c := by simpa [c] using hrad
    exact_mod_cast hnat
  have hliftBound : liftedL1 baseLift xLift ≤ 4 * (c : ℤ) := by
    rw [hdistLift]
    exact hdistZ
  have hdx : |xLift.1 - baseLift.1| ≤ 4 * (c : ℤ) := by
    unfold liftedL1 at hliftBound
    have hnonneg : 0 ≤ |xLift.2 - baseLift.2| := abs_nonneg _
    omega
  have hdy : |xLift.2 - baseLift.2| ≤ 4 * (c : ℤ) := by
    unfold liftedL1 at hliftBound
    have hnonneg : 0 ≤ |xLift.1 - baseLift.1| := abs_nonneg _
    omega
  have huBaseLtNat : uBase < 2 * c := by
    have h := Finset.mem_range.mp huBase
    rw [hside] at h
    simpa [c] using h
  have hvBaseLtNat : vBase < 2 * c := by
    have h := Finset.mem_range.mp hvBase
    rw [hside] at h
    simpa [c] using h
  have hbaseCoord1 : baseLift.1 = (a.1.val : ℤ) + uBase := by
    dsimp [baseLift]
  have hbaseCoord2 : baseLift.2 = (a.2.val : ℤ) + vBase := by
    dsimp [baseLift]
  have hxlo : -(4 * (c : ℤ)) ≤ xLift.1 - (a.1.val : ℤ) := by
    have hdx' := abs_le.mp hdx
    rw [hbaseCoord1] at hdx'
    omega
  have hxhi : xLift.1 - (a.1.val : ℤ) < 6 * (c : ℤ) := by
    have hdx' := abs_le.mp hdx
    have huLt : (uBase : ℤ) < 2 * (c : ℤ) := by exact_mod_cast huBaseLtNat
    rw [hbaseCoord1] at hdx'
    omega
  have hylo : -(4 * (c : ℤ)) ≤ xLift.2 - (a.2.val : ℤ) := by
    have hdy' := abs_le.mp hdy
    rw [hbaseCoord2] at hdy'
    omega
  have hyhi : xLift.2 - (a.2.val : ℤ) < 6 * (c : ℤ) := by
    have hdy' := abs_le.mp hdy
    have hvLt : (vBase : ℤ) < 2 * (c : ℤ) := by exact_mod_cast hvBaseLtNat
    rw [hbaseCoord2] at hdy'
    omega
  let zx := xLift.1 - (a.1.val : ℤ)
  let zy := xLift.2 - (a.2.val : ℤ)
  obtain ⟨i, u, hux⟩ := exists_basicLemmaCellCoordinates c hc zx hxlo hxhi
  obtain ⟨j, v, hvy⟩ := exists_basicLemmaCellCoordinates c hc zy hylo hyhi
  let vx : Fin (2 * c) := ⟨uBase, huBaseLtNat⟩
  let vy : Fin (2 * c) := ⟨vBase, hvBaseLtNat⟩
  have hvx : (vx.val : ℤ) = uBase := by rfl
  have hvy' : (vy.val : ℤ) = vBase := by rfl
  have hgapx := basicLemmaCellGap_le_abs c i u vx
  have hgapy := basicLemmaCellGap_le_abs c j v vy
  have hrelx : -(4 * (c : ℤ)) + (i.val : ℤ) * c + u.val - vx.val =
      xLift.1 - baseLift.1 := by
    dsimp [zx] at hux
    dsimp [baseLift]
    rw [← hux, hvx]
    ring
  have hrely : -(4 * (c : ℤ)) + (j.val : ℤ) * c + v.val - vy.val =
      xLift.2 - baseLift.2 := by
    dsimp [zy] at hvy
    dsimp [baseLift]
    rw [← hvy, hvy']
    ring
  rw [hrelx] at hgapx
  rw [hrely] at hgapy
  have hgap :
      (basicLemmaCellGap c i + basicLemmaCellGap c j : ℤ) ≤ 4 * (c : ℤ) := by
    calc
      _ ≤ |xLift.1 - baseLift.1| + |xLift.2 - baseLift.2| := add_le_add hgapx hgapy
      _ = liftedL1 baseLift xLift := rfl
      _ ≤ 4 * (c : ℤ) := hliftBound
  have hgapNat : basicLemmaCellGap c i + basicLemmaCellGap c j ≤ 4 * c := by
    exact_mod_cast hgap
  let cellLift : LiftedPoint :=
    ((a.1.val : ℤ) - 4 * c + (i.val : ℤ) * c,
      (a.2.val : ℤ) - 4 * c + (j.val : ℤ) * c)
  have hcellBox : xLift ∈ liftedSquare c cellLift := by
    change cellLift.1 ≤ xLift.1 ∧ xLift.1 ≤ cellLift.1 + (c : ℤ) - 1 ∧
      cellLift.2 ≤ xLift.2 ∧ xLift.2 ≤ cellLift.2 + (c : ℤ) - 1
    have hu0 : 0 ≤ (u.val : ℤ) := by positivity
    have hv0 : 0 ≤ (v.val : ℤ) := by positivity
    have huc : (u.val : ℤ) < c := by exact_mod_cast u.isLt
    have hvc : (v.val : ℤ) < c := by exact_mod_cast v.isLt
    have hux' := hux
    have hvy'' := hvy
    dsimp [zx] at hux'
    dsimp [zy] at hvy''
    dsimp [cellLift]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  have hKlt : squareSide (k - 2) < L := by
    have hpos : 0 < squareSide (k - 2) := Nat.pow_pos (by decide)
    omega
  have hcell := periodicProjection_mem_kpSquare_of_mem_liftedSquare
    L (k - 2) hLpos hKlt cellLift xLift hcellBox
  have hcellX : x ∈ kpSquare .periodic L (k - 2)
      (periodicProjection L hLpos cellLift) := by rw [← hxProj]; exact hcell
  refine ⟨i, j, hgapNat, ?_⟩
  simpa [basicLemmaFineCell, basicLemmaCellStart, cellLift] using hcellX

private theorem basicLemmaNeighborhood_has_nearbySupportPoint {L : ℕ}
    (boundary : SquareBoundary) (k : ℕ)
    (ρ q : ChargeDensity L) (hρ : ρ ≠ 0) (hq : q ≠ 0)
    (hnear : densityDistance boundary L q ρ ≤ 2 ^ k) :
    ∃ x ∈ chargeSupport q, ∃ y ∈ chargeSupport ρ,
      latticeDistance boundary L x y ≤ 2 ^ k := by
  have hsupp (f : ChargeDensity L) (hf : f ≠ 0) : (chargeSupport f).Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      apply hf
      funext x
      by_contra hx
      exact (h ⟨x, hx⟩).elim
    exact ⟨x, by simp [chargeSupport, hx]⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_squareDistance_eq boundary L
    (chargeSupport q) (chargeSupport ρ) (hsupp q hq) (hsupp ρ hρ)
  refine ⟨x, hx, y, hy, ?_⟩
  change squareDistance boundary L (chargeSupport q) (chargeSupport ρ) ≤ 2 ^ k at hnear
  rw [hxy] at hnear
  exact hnear

/-- A neighborhood of radius `R` has at most `M` times the support size
members whenever every radius-`R` ball has at most `M` sites. The disjoint
source supports inject these densities into the union of those balls. -/
theorem basicLemmaNeighborhood_card_le_ballBound {L : ℕ}
    (boundary : SquareBoundary) (k R M : ℕ) (E : ChargeEnsemble L)
    (hE : IsBKTEnsemble E) (ρ : ChargeDensity L) (hρ : ρ ≠ 0)
    (hR : 2 ^ k = R)
    (hball : ∀ y : Fin L × Fin L,
      (Finset.univ.filter fun x : Fin L × Fin L =>
        latticeDistance boundary L x y ≤ R).card ≤ M) :
    (basicLemmaNeighborhood boundary k E ρ).card ≤ M * (chargeSupport ρ).card := by
  classical
  let N := basicLemmaNeighborhood boundary k E ρ
  let B : Finset (Fin L × Fin L) :=
    (chargeSupport ρ).biUnion fun y =>
      Finset.univ.filter fun x => latticeDistance boundary L x y ≤ R
  have hρsupp : (chargeSupport ρ).Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, ρ x ≠ 0 := by
      by_contra h
      apply hρ
      funext x
      by_contra hx
      exact (h ⟨x, hx⟩).elim
    exact ⟨x, by simp [chargeSupport, hx]⟩
  have hfind : ∀ q ∈ N, ∃ x, x ∈ chargeSupport q ∧ x ∈ B := by
    intro q hq
    have hqE : q ∈ E := (Finset.mem_filter.mp hq).1
    have hqne := hE.1 q hqE
    have hdist : densityDistance boundary L q ρ ≤ 2 ^ k := by
      exact (Finset.mem_filter.mp hq).2
    obtain ⟨x, hx, y, hy, hxy⟩ :=
    basicLemmaNeighborhood_has_nearbySupportPoint boundary k ρ q hρ hqne hdist
    refine ⟨x, hx, Finset.mem_biUnion.mpr ⟨y, hy, ?_⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hR]
    exact hxy
  let f : ChargeDensity L → Fin L × Fin L := fun q =>
    if hq : q ∈ N then Classical.choose (hfind q hq) else Classical.choose hρsupp
  have hf : ∀ q ∈ N, f q ∈ chargeSupport q ∧ f q ∈ B := by
    intro q hq
    simpa [f, hq] using Classical.choose_spec (hfind q hq)
  have hinj : ∀ q ∈ N, ∀ r ∈ N, f q = f r → q = r := by
    intro q hq r hr hfr
    by_contra hqr
    have hqE : q ∈ E := (Finset.mem_filter.mp hq).1
    have hrE : r ∈ E := (Finset.mem_filter.mp hr).1
    have hdisj := hE.2 q hqE r hrE hqr
    have hxq : (f q) ∈ Function.support q := by
      simpa [chargeSupport, Function.mem_support] using (hf q hq).1
    have hxr : (f r) ∈ Function.support r := by
      simpa [chargeSupport, Function.mem_support] using (hf r hr).1
    rw [hfr] at hxq
    exact (Set.disjoint_left.mp hdisj) hxq hxr
  have hN : N.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn f (fun q hq => (hf q hq).2)
    intro q hq r hr hfr
    exact hinj q hq r hr hfr
  have hB : B.card ≤ M * (chargeSupport ρ).card := by
    calc
      B.card ≤ ∑ y ∈ chargeSupport ρ,
          (Finset.univ.filter fun x : Fin L × Fin L =>
            latticeDistance boundary L x y ≤ R).card := Finset.card_biUnion_le
      _ ≤ ∑ _y ∈ chargeSupport ρ, M := by
        apply Finset.sum_le_sum
        intro y hy
        exact hball y
      _ = M * (chargeSupport ρ).card := by simp [Nat.mul_comm]
  exact hN.trans hB

/-- The low-scale neighborhood count uses the exact lattice diamonds of sizes
five and thirteen. -/
theorem basicLemmaNeighborhood_count_small_scale {L : ℕ}
    (boundary : SquareBoundary) (k : ℕ) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble boundary E (basicLemmaPreviousScale k))
    (ρ : ChargeDensity L) (hρ : IsCompatible E ρ) (hk : k ≤ 1) :
    (basicLemmaNeighborhood boundary k E ρ).card ≤
      76 * chargeA boundary L ρ (basicLemmaPreviousScale k) := by
  have hk0 : k = 0 ∨ k = 1 := by omega
  rcases hk0 with rfl | rfl
  · have hsmall := basicLemmaNeighborhood_card_le_ballBound boundary 0 1 5 E hE.1 ρ hρ.1
      (by norm_num) (fun y => basicLemmaBall_radius_one_card_le boundary L y)
    calc
      (basicLemmaNeighborhood boundary 0 E ρ).card ≤ 5 * (chargeSupport ρ).card := hsmall
      _ ≤ 76 * chargeA boundary L ρ .minusOne := by simp [chargeA]; omega
  · have hsmall := basicLemmaNeighborhood_card_le_ballBound boundary 1 2 13 E hE.1 ρ hρ.1
      (by norm_num) (fun y => basicLemmaBall_radius_two_card_le boundary L y)
    calc
      (basicLemmaNeighborhood boundary 1 E ρ).card ≤ 13 * (chargeSupport ρ).card := hsmall
      _ ≤ 76 * chargeA boundary L ρ (.ofNat 0) := by simp [chargeA]; omega

/-- Fine cells attached to every square of a chosen coarse cover. -/
noncomputable def basicLemmaCellsForCover (boundary : SquareBoundary) (L m : ℕ)
    (hL : 1 < L) (hbase : 2 * squareSide m ≤ L)
    (C : Finset (Finset (Fin L × Fin L))) :
    Finset (Finset (Fin L × Fin L)) :=
  C.biUnion fun S => basicLemmaCellsForSquare boundary L m hL hbase
    (squareAnchor boundary L (m + 1) (by omega) S)

theorem basicLemmaCellsForCover_card_le (boundary : SquareBoundary) (L m : ℕ)
    (hL : 1 < L) (hbase : 2 * squareSide m ≤ L)
    (C : Finset (Finset (Fin L × Fin L))) :
    (basicLemmaCellsForCover boundary L m hL hbase C).card ≤ 76 * C.card := by
  unfold basicLemmaCellsForCover
  calc
    _ ≤ ∑ S ∈ C,
        (basicLemmaCellsForSquare boundary L m hL hbase
          (squareAnchor boundary L (m + 1) (by omega) S)).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ C, 76 := by
      apply Finset.sum_le_sum
      intro S hS
      exact basicLemmaCellsForSquare_card_le boundary L m hL hbase _
    _ = 76 * C.card := by simp [Nat.mul_comm]

theorem basicLemmaCellsForCover_diameter_le (boundary : SquareBoundary) (L m : ℕ)
    (hL : 1 < L) (hbase : 2 * squareSide m ≤ L)
    (C : Finset (Finset (Fin L × Fin L)))
    (S : Finset (Fin L × Fin L)) (hS : S ∈ basicLemmaCellsForCover boundary L m hL hbase C) :
    squareDiameter boundary L S ≤ 2 ^ (m + 1) := by
  classical
  unfold basicLemmaCellsForCover at hS
  obtain ⟨T, hTC, hS⟩ := Finset.mem_biUnion.mp hS
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨_, hgap⟩ := Finset.mem_filter.mp hp
  have hdiam := basicLemmaFineCell_diameter_le boundary L m hL hbase
    (squareAnchor boundary L (m + 1) (by omega) T) p.1 p.2
  have hpow : 2 ^ (m + 1) = 2 * squareSide m := by
    simp [squareSide, pow_succ, Nat.mul_comm]
  rw [hpow]
  have hcpos : 0 < squareSide m := Nat.pow_pos (by decide)
  omega

/-- The normal free-box count, with clipping handled by the fine-cell cover. -/
theorem basicLemmaNeighborhood_count_free_normal {L m : ℕ}
    (hL : 1 < L) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble .free E (.ofNat (m + 1)))
    (ρ : ChargeDensity L) (hρ : IsCompatible E ρ)
    (hbase : 2 * squareSide m ≤ L) :
    (basicLemmaNeighborhood .free (m + 2) E ρ).card ≤
      76 * chargeA .free L ρ (.ofNat (m + 1)) := by
  classical
  obtain ⟨C, hC⟩ := exists_minimumSquareCover .free L (m + 1) ρ
  have hCcard : C.card = squareCoverNumber .free L (m + 1) ρ :=
    card_eq_squareCoverNumber_of_isMinimumSquareCover .free L (m + 1) ρ C hC
  let Cells := basicLemmaCellsForCover .free L m hL hbase C
  have hdiam : ∀ S ∈ Cells,
      squareDiameter .free L S ≤ ChargeScale.separationThreshold (.ofNat (m + 1)) := by
    intro S hS
    simpa [ChargeScale.separationThreshold] using
      basicLemmaCellsForCover_diameter_le .free L m hL hbase C S hS
  have hcover : ∀ q ∈ basicLemmaNeighborhood .free (m + 2) E ρ,
      ∃ S ∈ Cells, ∃ x ∈ chargeSupport q, x ∈ S := by
    intro q hq
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      basicLemmaNeighborhood_has_nearbySupportPoint .free (m + 2) ρ q hρ.1
        (hE.1.1 q (Finset.mem_filter.mp hq).1) (Finset.mem_filter.mp hq).2
    obtain ⟨T, hT, hyT⟩ := hC.1.2 y hy
    let a := squareAnchor .free L (m + 1) (by omega) T
    have hTmem : T ∈ kpSquares .free L (m + 1) := hC.1.1 hT
    have hTrepr : kpSquare .free L (m + 1) a = T := by
      exact kpSquare_eq_of_squareAnchor .free L (m + 1) (by omega) T hTmem
    have hySquare : y ∈ kpSquare .free L (m + 1) a := hTrepr ▸ hyT
    obtain ⟨i, j, hgap, hxcell⟩ := basicLemmaFreeFineCell_covering L (m + 2)
      (by omega) hL hbase a x y hySquare hxy
    refine ⟨basicLemmaFineCell .free L m hL hbase a i j, ?_, x, hx, hxcell⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨T, hT, ?_⟩
    unfold basicLemmaCellsForSquare
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgap⟩, rfl⟩
  have hcount := basicLemmaNeighborhood_card_le_cellCover .free (m + 2) E
    (by simpa [basicLemmaPreviousScale] using hE) ρ Cells hdiam hcover
  calc
    (basicLemmaNeighborhood .free (m + 2) E ρ).card ≤ Cells.card := hcount
    _ ≤ 76 * C.card := basicLemmaCellsForCover_card_le .free L m hL hbase C
    _ = 76 * chargeA .free L ρ (.ofNat (m + 1)) := by
      rw [hCcard]
      rfl

/-- The normal periodic-box count; the strict side inequality lets each
coarse quotient square be lifted without a collapsed tile. -/
theorem basicLemmaNeighborhood_count_periodic_normal {L m : ℕ}
    (hL : 1 < L) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble .periodic E (.ofNat (m + 1)))
    (ρ : ChargeDensity L) (hρ : IsCompatible E ρ)
    (hbase : 2 * squareSide m < L) :
    (basicLemmaNeighborhood .periodic (m + 2) E ρ).card ≤
      76 * chargeA .periodic L ρ (.ofNat (m + 1)) := by
  classical
  obtain ⟨C, hC⟩ := exists_minimumSquareCover .periodic L (m + 1) ρ
  have hCcard : C.card = squareCoverNumber .periodic L (m + 1) ρ :=
    card_eq_squareCoverNumber_of_isMinimumSquareCover .periodic L (m + 1) ρ C hC
  let Cells := basicLemmaCellsForCover .periodic L m hL (by omega) C
  have hdiam : ∀ S ∈ Cells,
      squareDiameter .periodic L S ≤ ChargeScale.separationThreshold (.ofNat (m + 1)) := by
    intro S hS
    simpa [ChargeScale.separationThreshold] using
      basicLemmaCellsForCover_diameter_le .periodic L m hL (by omega) C S hS
  have hcover : ∀ q ∈ basicLemmaNeighborhood .periodic (m + 2) E ρ,
      ∃ S ∈ Cells, ∃ x ∈ chargeSupport q, x ∈ S := by
    intro q hq
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      basicLemmaNeighborhood_has_nearbySupportPoint .periodic (m + 2) ρ q hρ.1
        (hE.1.1 q (Finset.mem_filter.mp hq).1) (Finset.mem_filter.mp hq).2
    obtain ⟨T, hT, hyT⟩ := hC.1.2 y hy
    let a := squareAnchor .periodic L (m + 1) (by omega) T
    have hTmem : T ∈ kpSquares .periodic L (m + 1) := hC.1.1 hT
    have hTrepr : kpSquare .periodic L (m + 1) a = T := by
      exact kpSquare_eq_of_squareAnchor .periodic L (m + 1) (by omega) T hTmem
    have hySquare : y ∈ kpSquare .periodic L (m + 1) a := hTrepr ▸ hyT
    obtain ⟨i, j, hgap, hxcell⟩ := basicLemmaPeriodicFineCell_covering L (m + 2)
      (by omega) hL hbase a x y hySquare hxy
    refine ⟨basicLemmaFineCell .periodic L m hL (by omega) a i j, ?_, x, hx, hxcell⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨T, hT, ?_⟩
    unfold basicLemmaCellsForSquare
    apply Finset.mem_image.mpr
    refine ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgap⟩, rfl⟩
  have hcount := basicLemmaNeighborhood_card_le_cellCover .periodic (m + 2) E
    (by simpa [basicLemmaPreviousScale] using hE) ρ Cells hdiam hcover
  calc
    (basicLemmaNeighborhood .periodic (m + 2) E ρ).card ≤ Cells.card := hcount
    _ ≤ 76 * C.card := basicLemmaCellsForCover_card_le .periodic L m hL (by omega) C
    _ = 76 * chargeA .periodic L ρ (.ofNat (m + 1)) := by
      rw [hCcard]
      rfl

/-- A fine-scale statement used by the four-cell overflow cover. The free cover
clips its second interval at `L`; the periodic cover starts the second interval
at `c`. -/
noncomputable def basicLemmaOverflowAnchor (boundary : SquareBoundary) (L m : ℕ)
    (hL : 0 < L) (hc : squareSide m < L) (i : Fin 2) : Fin L := by
  have hcpos : 0 < squareSide m := Nat.pow_pos (by decide)
  cases boundary with
  | free =>
      exact if i.val = 0 then ⟨0, hL⟩ else ⟨L - squareSide m, by omega⟩
  | periodic =>
      exact if i.val = 0 then ⟨0, hL⟩ else ⟨squareSide m, hc⟩

private theorem basicLemmaOverflowFreeCoordinate (L m : ℕ) (hL : 0 < L)
    (hc : squareSide m < L) (hwide : L < 2 * squareSide m)
    (z : ℕ) (hz : z < L) :
    ∃ i : Fin 2,
      (basicLemmaOverflowAnchor .free L m hL hc i).val ≤ z ∧
        z < (basicLemmaOverflowAnchor .free L m hL hc i).val + squareSide m := by
  by_cases hzc : z < squareSide m
  · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
    · simp [basicLemmaOverflowAnchor]
    · simp [basicLemmaOverflowAnchor]
      omega
  · refine ⟨⟨1, by omega⟩, ?_, ?_⟩
    · simp [basicLemmaOverflowAnchor]
      omega
    · simp [basicLemmaOverflowAnchor]
      omega

private theorem basicLemmaOverflowPeriodicCoordinate (L m : ℕ) (hL : 0 < L)
    (hc : squareSide m < L) (hwide : L ≤ 2 * squareSide m)
    (z : ℕ) (hz : z < L) :
    ∃ i : Fin 2, ∃ n ∈ Finset.range (squareSide m),
      z = ((basicLemmaOverflowAnchor .periodic L m hL hc i).val + n) % L := by
  by_cases hzc : z < squareSide m
  · let i : Fin 2 := ⟨0, by omega⟩
    have hanchor : (basicLemmaOverflowAnchor .periodic L m hL hc i).val = 0 := by
      simp [basicLemmaOverflowAnchor, i]
    refine ⟨i, z, Finset.mem_range.mpr hzc, ?_⟩
    rw [hanchor, Nat.zero_add, Nat.mod_eq_of_lt hz]
  · let i : Fin 2 := ⟨1, by omega⟩
    have hanchor : (basicLemmaOverflowAnchor .periodic L m hL hc i).val = squareSide m := by
      simp [basicLemmaOverflowAnchor, i]
    refine ⟨i, z - squareSide m,
      Finset.mem_range.mpr (by omega), ?_⟩
    have hsum : squareSide m + (z - squareSide m) = z := by omega
    rw [hanchor]
    rw [hsum, Nat.mod_eq_of_lt hz]

/-- Four clipped or wrapped fine squares cover the whole box in the overflow
regime where one fine side is smaller than the box. -/
noncomputable def basicLemmaOverflowCells (boundary : SquareBoundary) (L m : ℕ)
    (hL : 0 < L) (hc : squareSide m < L) :
    Finset (Finset (Fin L × Fin L)) :=
  (Finset.univ : Finset (Fin 2 × Fin 2)).image fun p =>
    kpSquare boundary L m
      (basicLemmaOverflowAnchor boundary L m hL hc p.1,
        basicLemmaOverflowAnchor boundary L m hL hc p.2)

theorem basicLemmaOverflowCells_card_le_four (boundary : SquareBoundary) (L m : ℕ)
    (hL : 0 < L) (hc : squareSide m < L) :
    (basicLemmaOverflowCells boundary L m hL hc).card ≤ 4 := by
  unfold basicLemmaOverflowCells
  calc
    _ ≤ (Finset.univ : Finset (Fin 2 × Fin 2)).card := Finset.card_image_le
    _ = 4 := by norm_num

theorem basicLemmaOverflowCells_diameter_le (boundary : SquareBoundary) (L m : ℕ)
    (hL : 1 < L) (hc : squareSide m < L)
    (S : Finset (Fin L × Fin L)) (hS : S ∈ basicLemmaOverflowCells boundary L m (by omega) hc) :
    squareDiameter boundary L S ≤ 2 ^ (m + 1) := by
  obtain ⟨p, -, hEq⟩ := Finset.mem_image.mp hS
  have hmem : kpSquare boundary L m
      (basicLemmaOverflowAnchor boundary L m (by omega) hc p.1,
       basicLemmaOverflowAnchor boundary L m (by omega) hc p.2) ∈ kpSquares boundary L m :=
    Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hdiam : squareDiameter boundary L
      (kpSquare boundary L m
        (basicLemmaOverflowAnchor boundary L m (by omega) hc p.1,
         basicLemmaOverflowAnchor boundary L m (by omega) hc p.2)) ≤
      2 * (squareSide m - 1) := by
    cases boundary with
    | free => exact free_squareDiameter_le_all L m _ hmem
    | periodic => exact periodic_squareDiameter_le L m hL _ hmem
  have hpow : 2 ^ (m + 1) = 2 * squareSide m := by
    simp [squareSide, pow_succ, Nat.mul_comm]
  have hcpos : 0 < squareSide m := Nat.pow_pos (by decide)
  calc
    squareDiameter boundary L S = squareDiameter boundary L
        (kpSquare boundary L m
          (basicLemmaOverflowAnchor boundary L m (by omega) hc p.1,
           basicLemmaOverflowAnchor boundary L m (by omega) hc p.2)) := by rw [hEq]
    _ ≤ 2 * (squareSide m - 1) := hdiam
    _ ≤ 2 ^ (m + 1) := by rw [hpow]; omega

theorem basicLemmaOverflowCells_cover_free (L m : ℕ) (hL : 0 < L)
    (hc : squareSide m < L) (hwide : L < 2 * squareSide m)
    (x : Fin L × Fin L) :
    ∃ S ∈ basicLemmaOverflowCells .free L m hL hc, x ∈ S := by
  obtain ⟨i, hixlo, hixhi⟩ := basicLemmaOverflowFreeCoordinate L m hL hc hwide
    x.1.val x.1.isLt
  obtain ⟨j, hjylo, hjyhi⟩ := basicLemmaOverflowFreeCoordinate L m hL hc hwide
    x.2.val x.2.isLt
  let a := (basicLemmaOverflowAnchor .free L m hL hc i,
    basicLemmaOverflowAnchor .free L m hL hc j)
  have hxmem : x ∈ kpSquare .free L m a := by
    rw [mem_kpSquare_free_iff L m (by omega) a x]
    exact ⟨hixlo, hixhi, hjylo, hjyhi⟩
  refine ⟨kpSquare .free L m a, ?_, hxmem⟩
  unfold basicLemmaOverflowCells
  apply Finset.mem_image.mpr
  refine ⟨(i, j), Finset.mem_univ _, ?_⟩
  rfl

theorem basicLemmaOverflowCells_cover_periodic (L m : ℕ) (hL : 0 < L)
    (hc : squareSide m < L) (hwide : L ≤ 2 * squareSide m)
    (x : Fin L × Fin L) :
    ∃ S ∈ basicLemmaOverflowCells .periodic L m hL hc, x ∈ S := by
  obtain ⟨i, u, hu, hix⟩ := basicLemmaOverflowPeriodicCoordinate L m hL hc hwide
    x.1.val x.1.isLt
  obtain ⟨j, v, hv, hjy⟩ := basicLemmaOverflowPeriodicCoordinate L m hL hc hwide
    x.2.val x.2.isLt
  let a := (basicLemmaOverflowAnchor .periodic L m hL hc i,
    basicLemmaOverflowAnchor .periodic L m hL hc j)
  have hxmem : x ∈ kpSquare .periodic L m a := by
    apply (mem_kpSquare_periodic_iff L m hc a x).2
    exact ⟨u, hu, v, hv, by simpa [a] using hix, by simpa [a] using hjy⟩
  refine ⟨kpSquare .periodic L m a, ?_, hxmem⟩
  unfold basicLemmaOverflowCells
  apply Finset.mem_image.mpr
  refine ⟨(i, j), Finset.mem_univ _, ?_⟩
  rfl

theorem basicLemmaNeighborhood_card_le_domainCells {L : ℕ}
    (boundary : SquareBoundary) (k : ℕ) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble boundary E (basicLemmaPreviousScale k))
    (ρ : ChargeDensity L)
    (Cells : Finset (Finset (Fin L × Fin L)))
    (hdiam : ∀ S ∈ Cells,
      squareDiameter boundary L S ≤
        ChargeScale.separationThreshold (basicLemmaPreviousScale k))
    (hcover : ∀ x : Fin L × Fin L, ∃ S ∈ Cells, x ∈ S) :
    (basicLemmaNeighborhood boundary k E ρ).card ≤ Cells.card := by
  apply basicLemmaNeighborhood_card_le_cellCover boundary k E hE ρ Cells hdiam
  intro q hq
  have hqne := hE.1.1 q (Finset.mem_filter.mp hq).1
  have hsupp : (chargeSupport q).Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, q x ≠ 0 := by
      by_contra h
      apply hqne
      funext x
      by_contra hx
      exact (h ⟨x, hx⟩).elim
    exact ⟨x, by simp [chargeSupport, hx]⟩
  obtain ⟨x, hx⟩ := hsupp
  obtain ⟨S, hS, hxS⟩ := hcover x
  exact ⟨S, hS, x, hx, hxS⟩

theorem chargeA_positive_of_nonzero (boundary : SquareBoundary) (L m : ℕ)
    (ρ : ChargeDensity L) (hρ : ρ ≠ 0) :
    0 < chargeA boundary L ρ (.ofNat (m + 1)) := by
  change 0 < squareCoverNumber boundary L (m + 1) ρ
  have hsupp : (chargeSupport ρ).Nonempty := by
    obtain ⟨x, hx⟩ : ∃ x, ρ x ≠ 0 := by
      by_contra h
      apply hρ
      funext x
      by_contra hx
      exact (h ⟨x, hx⟩).elim
    exact ⟨x, by simp [chargeSupport, hx]⟩
  obtain ⟨x, hx⟩ := hsupp
  obtain ⟨C, hC, hcard⟩ := exists_squareCover_attaining_number boundary L (m + 1) ρ
  have hCne : C.Nonempty := by
    by_contra hCempty
    have hCeq : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCempty
    obtain ⟨S, hS, hxS⟩ := hC.2 x hx
    rw [hCeq] at hS
    exact Finset.notMem_empty S hS
  rw [← hcard]
  exact Finset.card_pos.mpr hCne

theorem basicLemmaOverflow_fullSquare_eq_univ (boundary : SquareBoundary) (L m : ℕ)
    (hL : 0 < L) (hc : L ≤ squareSide m) :
    kpSquare boundary L m (⟨0, hL⟩, ⟨0, hL⟩) = Finset.univ := by
  cases boundary with
  | free =>
      by_cases hgt : squareSide m > L
      · simp [kpSquare, hgt]
      · have heq : squareSide m = L := by omega
        ext x
        simp only [kpSquare, hgt, ↓reduceIte, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> intro hx
        · trivial
        · exact ⟨by omega, by rw [heq]; omega,
            by omega, by rw [heq]; omega⟩
  | periodic =>
      simp [kpSquare, show squareSide m ≥ L by omega]

private theorem basicLemmaOverflowCount_from_fourCells {L m : ℕ}
    (boundary : SquareBoundary) (_hL : 1 < L)
    (E : ChargeEnsemble L) (hE : IsChargeScaleEnsemble boundary E (.ofNat (m + 1)))
    (ρ : ChargeDensity L) (hρ : IsCompatible E ρ)
    (Cells : Finset (Finset (Fin L × Fin L)))
    (hcard : Cells.card ≤ 4)
    (hdiam : ∀ S ∈ Cells,
      squareDiameter boundary L S ≤ ChargeScale.separationThreshold (.ofNat (m + 1)))
    (hcover : ∀ x : Fin L × Fin L, ∃ S ∈ Cells, x ∈ S) :
    (basicLemmaNeighborhood boundary (m + 2) E ρ).card ≤
      76 * chargeA boundary L ρ (.ofNat (m + 1)) := by
  have hcount := basicLemmaNeighborhood_card_le_domainCells boundary (m + 2) E
    (by simpa [basicLemmaPreviousScale] using hE) ρ Cells
    (by simpa [basicLemmaPreviousScale] using hdiam) hcover
  have hA := chargeA_positive_of_nonzero boundary L m ρ hρ.1
  omega

private theorem basicLemmaOverflowCount_from_fullCell {L m : ℕ}
    (boundary : SquareBoundary) (hL : 1 < L)
    (E : ChargeEnsemble L) (hE : IsChargeScaleEnsemble boundary E (.ofNat (m + 1)))
    (ρ : ChargeDensity L) (hρ : IsCompatible E ρ)
    (hc : L ≤ squareSide m) :
    (basicLemmaNeighborhood boundary (m + 2) E ρ).card ≤
      76 * chargeA boundary L ρ (.ofNat (m + 1)) := by
  let a : Fin L × Fin L := (⟨0, by omega⟩, ⟨0, by omega⟩)
  let F := kpSquare boundary L m a
  let Cells : Finset (Finset (Fin L × Fin L)) := {F}
  have hwhole : F = Finset.univ := by
    simpa [F, a] using basicLemmaOverflow_fullSquare_eq_univ boundary L m (by omega) hc
  have hmem : F ∈ kpSquares boundary L m := by
    unfold F
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hdiamF : squareDiameter boundary L F ≤ 2 * (squareSide m - 1) := by
    cases boundary with
    | free => exact free_squareDiameter_le_all L m F hmem
    | periodic => exact periodic_squareDiameter_le L m hL F hmem
  have hpow : 2 ^ (m + 1) = 2 * squareSide m := by
    simp [squareSide, pow_succ, Nat.mul_comm]
  have hdiam : ∀ S ∈ Cells,
      squareDiameter boundary L S ≤ ChargeScale.separationThreshold (.ofNat (m + 1)) := by
    intro S hS
    have hSF : S = F := by simpa [Cells] using hS
    subst S
    rw [ChargeScale.separationThreshold, hpow]
    have hcpos : 0 < squareSide m := Nat.pow_pos (by decide)
    omega
  have hcover : ∀ x : Fin L × Fin L, ∃ S ∈ Cells, x ∈ S := by
    intro x
    refine ⟨F, by simp [Cells], ?_⟩
    rw [hwhole]
    simp
  exact basicLemmaOverflowCount_from_fourCells boundary hL E hE ρ hρ Cells
    (by simp [Cells]) hdiam hcover

theorem basicLemmaNeighborhood_count_free_overflow {L m : ℕ}
    (hL : 1 < L) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble .free E (.ofNat (m + 1)))
    (ρ : ChargeDensity L) (hρ : IsCompatible E ρ)
    (hoverflow : L < 2 * squareSide m) :
    (basicLemmaNeighborhood .free (m + 2) E ρ).card ≤
      76 * chargeA .free L ρ (.ofNat (m + 1)) := by
  by_cases hc : squareSide m < L
  · let Cells := basicLemmaOverflowCells .free L m (by omega) hc
    have hdiam : ∀ S ∈ Cells,
        squareDiameter .free L S ≤ ChargeScale.separationThreshold (.ofNat (m + 1)) := by
      intro S hS
      simpa [ChargeScale.separationThreshold] using
        basicLemmaOverflowCells_diameter_le .free L m hL hc S hS
    have hcover : ∀ x : Fin L × Fin L, ∃ S ∈ Cells, x ∈ S := by
      intro x
      obtain ⟨S, hS, hx⟩ := basicLemmaOverflowCells_cover_free L m (by omega) hc hoverflow x
      exact ⟨S, by simpa [Cells] using hS, hx⟩
    exact basicLemmaOverflowCount_from_fourCells .free hL E hE ρ hρ Cells
      (by simpa [Cells] using basicLemmaOverflowCells_card_le_four .free L m (by omega) hc)
      hdiam hcover
  · exact basicLemmaOverflowCount_from_fullCell .free hL E hE ρ hρ (by omega)

theorem basicLemmaNeighborhood_count_periodic_overflow {L m : ℕ}
    (hL : 1 < L) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble .periodic E (.ofNat (m + 1)))
    (ρ : ChargeDensity L) (hρ : IsCompatible E ρ)
    (hoverflow : L ≤ 2 * squareSide m) :
    (basicLemmaNeighborhood .periodic (m + 2) E ρ).card ≤
      76 * chargeA .periodic L ρ (.ofNat (m + 1)) := by
  by_cases hc : squareSide m < L
  · let Cells := basicLemmaOverflowCells .periodic L m (by omega) hc
    have hdiam : ∀ S ∈ Cells,
        squareDiameter .periodic L S ≤ ChargeScale.separationThreshold (.ofNat (m + 1)) := by
      intro S hS
      simpa [ChargeScale.separationThreshold] using
        basicLemmaOverflowCells_diameter_le .periodic L m hL hc S hS
    have hcover : ∀ x : Fin L × Fin L, ∃ S ∈ Cells, x ∈ S := by
      intro x
      obtain ⟨S, hS, hx⟩ := basicLemmaOverflowCells_cover_periodic L m (by omega) hc hoverflow x
      exact ⟨S, by simpa [Cells] using hS, hx⟩
    exact basicLemmaOverflowCount_from_fourCells .periodic hL E hE ρ hρ Cells
      (by simpa [Cells] using basicLemmaOverflowCells_card_le_four .periodic L m (by omega) hc)
      hdiam hcover
  · exact basicLemmaOverflowCount_from_fullCell .periodic hL E hE ρ hρ (by omega)

/--
's finite-square neighborhood count on both  carriers.

The
small scales use graph balls of size five and thirteen; larger scales use the
76-cell enlargement, including the four-cell overflow cover.
-/
theorem basicLemmaNeighborhood_count {L : ℕ} (boundary : SquareBoundary)
    (hL : 1 < L) (k : ℕ) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble boundary E (basicLemmaPreviousScale k))
    (ρ : ChargeDensity L) (hρ : IsCompatible E ρ) :
    (basicLemmaNeighborhood boundary k E ρ).card ≤
      76 * chargeA boundary L ρ (basicLemmaPreviousScale k) := by
  by_cases hk : k ≤ 1
  · exact basicLemmaNeighborhood_count_small_scale boundary k E hE ρ hρ hk
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨m, hkeq⟩ : ∃ m, k = m + 2 := by
      refine ⟨k - 2, ?_⟩
      omega
    rw [hkeq] at hE ⊢
    have hE' : IsChargeScaleEnsemble boundary E (.ofNat (m + 1)) := by
      simpa [basicLemmaPreviousScale] using hE
    cases boundary with
    | free =>
        by_cases hbase : 2 * squareSide m ≤ L
        · simpa [basicLemmaPreviousScale] using
            basicLemmaNeighborhood_count_free_normal hL E hE' ρ hρ hbase
        · have hoverflow : L < 2 * squareSide m := by omega
          simpa [basicLemmaPreviousScale] using
            basicLemmaNeighborhood_count_free_overflow hL E hE' ρ hρ hoverflow
    | periodic =>
        by_cases hbase : 2 * squareSide m < L
        · simpa [basicLemmaPreviousScale] using
            basicLemmaNeighborhood_count_periodic_normal hL E hE' ρ hρ hbase
        · have hoverflow : L ≤ 2 * squareSide m := by omega
          simpa [basicLemmaPreviousScale] using
            basicLemmaNeighborhood_count_periodic_overflow hL E hE' ρ hρ hoverflow

end FroehlichSpencer.BKT

end
