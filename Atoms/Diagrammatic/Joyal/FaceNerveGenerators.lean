import Atoms.Diagrammatic.Joyal.FaceNerveHorn
import Atoms.Diagrammatic.Marked.NaturalMarking

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP

universe u

namespace Atoms.Diagrammatic

open MarkedSSet.modelCategoryCartesian

section MoleculeHorn

variable (m : Shape.MarkedHornData)

theorem weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_isMoleculeIn
    (hA₁ : ∀ a ∈ m.targetMarking, grade ℕ a ≠ 1)
    (hout : outputRel m.atom.ogp m.face m.atom.top)
    (hmol : IsMoleculeIn m.atom.ogp m.hornSet)
    {t : m.atom.ogp} (ht : m.atom.ogp.boundary ⊤ 0 true = .Iic t)
    (htQ : t ∈ m.atom.ogp.boundary m.hornSet 0 true) :
    WeakEquivalence (markedFaceNerve.{u}.map (markedHornInclusion m)) := by
  have hQw : ∀ y ∈ m.hornSet, y < m.atom.top :=
    fun y hy => lt_of_le_of_ne (m.atom.le_top y) ((mem_hornSet_iff_ne_and_ne m).1 hy).2
  have := weakEquivalence_coneBase_of_isMoleculeIn
    (fun a b => outputRel m.atom.ogp a b ∧ b ≠ m.atom.top) (w := m.atom.top)
    (fun _ _ _ hb h => ⟨h, hb.ne⟩) (fun _ h => absurd rfl h.2) hmol hQw htQ
  exact weakEquivalence_markedFaceNerve_map_markedHornInclusion m hA₁ hout ht
    (boundary_le _ 0 true htQ)

end MoleculeHorn

section Compositor

variable (U : RoundShape) (hU : 0 < U.dimension)

theorem weakEquivalence_markedFaceNerve_map_compositorMarkedHorn :
    WeakEquivalence (markedFaceNerve.{u}.map
      (markedHornInclusion (Shape.compositorMarkedHorn U hU))) := by
  let m := Shape.compositorMarkedHorn U hU
  have hd : m.atom.dimension = U.dimension + 1 := Shape.dimension_toMergerAtom U hU
  have hd2 : 2 ≤ m.atom.dimension := by omega
  have hclosure : LowerSet.Iic m.face = m.atom.ogp.bdry ⊤ true :=
    Shape.closure_compositorFace U hU
  have hhorn : m.hornSet = m.atom.ogp.bdry ⊤ false :=
    (Shape.hornSet_compositorFace U hU).trans (U.map_inputIncl (Nat.sub_add_cancel hU).symm)
  obtain ⟨t, -, ht⟩ := exists_boundary_zero_eq_Iic m.atom.isMolecule true
  refine weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_isMoleculeIn m
    (fun a ha => ?_) ?_ (hhorn ▸ m.isMoleculeIn_bdry false) ht ?_
  · rcases m.mem_targetMarking_iff.1 ha with rfl | ⟨hsub, -⟩ | ha
    · rw [← m.atom.dimension_eq]
      omega
    · obtain ⟨y, hy⟩ := m.atom.isMolecule.nonempty_faces LowerSet.mem_top
        (by rw [← m.atom.dimension_eq]; omega) (!m.side)
      exact absurd (hsub hy) (Set.notMem_empty y)
    · exact absurd ha (Set.notMem_empty a)
  · change m.atom.ogp.boundary (.Iic m.face) 0 true = m.atom.ogp.boundary (.Iic m.atom.top) 0 true
    rw [hclosure, boundary_bdry_zero m.atom hd2, m.atom.Iic_top]
  · rw [hhorn, boundary_bdry_zero m.atom hd2, ht]
    exact LowerSet.mem_Iic_iff.2 le_rfl

end Compositor

section InvertorArrow

variable (V : Shape.Atom) (ε : Bool) (hV : 0 < V.dimension)

private theorem mem_targetMarking_invertorMarkedHorn_iff (h1 : V.dimension = 1)
    {b : (Shape.invertorMarkedHorn V ε hV).atom.ogp} :
    b ∈ (Shape.invertorMarkedHorn V ε hV).targetMarking ∧ grade ℕ b = 1 ↔
      b ∈ (Shape.invertorMarkedHorn V ε hV).marking ∧ grade ℕ b = 1 := by
  let m := Shape.invertorMarkedHorn V ε hV
  have hd : m.atom.dimension = 2 := by
    change (Shape.invertorAtom V ε hV).dimension = 2
    rw [Shape.dimension_invertorAtom, h1]
  refine ⟨fun ⟨hb, hb1⟩ => ⟨?_, hb1⟩, fun ⟨hb, hb1⟩ =>
    ⟨m.mem_targetMarking_iff.2 (Or.inr (Or.inr hb)), hb1⟩⟩
  rcases m.mem_targetMarking_iff.1 hb with rfl | ⟨hsub, -⟩ | hb
  · rw [← m.atom.dimension_eq, hd] at hb1
    exact absurd hb1 (by decide)
  · exfalso
    have htop : 0 < grade ℕ m.atom.top := by
      rw [← m.atom.dimension_eq, hd]
      exact Nat.two_pos
    obtain ⟨y, hy⟩ := m.atom.isMolecule.nonempty_faces LowerSet.mem_top htop (!m.side)
    have hy' : y ∈ ({Shape.invertorTopElt V ε hV (some (!ε))} : Set _) := hsub hy
    rw [Set.mem_singleton_iff.1 hy'] at hy
    have h₁ := hy.2
    have h₂ := (Shape.invertorTopElt_mem_faceSet V ε hV (!ε)).2
    have h₃ : m.side = !ε := rfl
    rw [h₃] at h₁
    have h₄ : (!!ε) = !ε := h₁.symm.trans h₂
    cases ε <;> exact absurd h₄ (by decide)
  · exact hb

private theorem invertorTopElt_ne_of_dimension_eq_one (h1 : V.dimension = 1) :
    Shape.invertorTopElt V ε hV (some false) ≠ Shape.invertorTopElt V ε hV (some true) ∧
      ∀ β, Shape.invertorTopElt V ε hV (some β) ≠ (Shape.invertorAtom V ε hV).top := by
  have hdim (β : Bool) := (Shape.dim_invertorTopElt_some V ε hV β).trans h1
  refine ⟨fun h => ?_, fun β h => ?_⟩
  · have he : Shape.invertorTopElt V ε hV (some ε) = Shape.invertorTopElt V ε hV (some (!ε)) := by
      cases ε
      exacts [h, h.symm]
    have h' := (Shape.isPastingIn_closure_invertorTopElt V ε hV).inf_eq_output
    rw [he, Bool.cond_self, inf_idem] at h'
    have := grade_le_of_mem_boundary ((congrArg (_ ∈ ·) h').mp (LowerSet.mem_Iic_iff.2 le_rfl))
    rw [hdim, Shape.dimension_invertorAtom, h1] at this
    omega
  · have h' := hdim β
    rw [h, ← (Shape.invertorAtom V ε hV).dimension_eq, Shape.dimension_invertorAtom, h1] at h'
    omega

private theorem weakEquivalence_markedFaceNerve_map_invertorMarkedHorn_true_of_dimension_eq_one
    (hV : 0 < V.dimension) (h1 : V.dimension = 1) :
    WeakEquivalence (markedFaceNerve.{u}.map
      (markedHornInclusion (Shape.invertorMarkedHorn V true hV))) := by
  let m := Shape.invertorMarkedHorn V true hV
  let L : m.atom.ogp := Shape.invertorTopElt V true hV (some false)
  let Rr : m.atom.ogp := Shape.invertorTopElt V true hV (some true)
  have hd : m.atom.dimension = 2 := by
    change (Shape.invertorAtom V true hV).dimension = 2
    rw [Shape.dimension_invertorAtom, h1]
  have hdim (β : Bool) : grade ℕ (Shape.invertorTopElt V true hV (some β)) =
      m.atom.dimension - 1 := by
    rw [hd]
    exact (Shape.dim_invertorTopElt_some V true hV β).trans h1
  have hp : m.atom.ogp.IsPastingIn (m.atom.dimension - 2) (.Iic L) (.Iic Rr)
      (m.atom.ogp.bdry ⊤ false) :=
    Shape.isPastingIn_closure_invertorTopElt V true hV
  have hgA := IsMoleculeIn.isGlobular (m.atom.isRDC L)
  have hgB := IsMoleculeIn.isGlobular (m.atom.isRDC Rr)
  have hQ : (m.hornSet : Set m.atom.ogp) =
      ((LowerSet.Iic L ⊔ m.atom.ogp.bdry ⊤ true : LowerSet m.atom.ogp) : Set m.atom.ogp) := by
    change (m.atom.ogp.bdryFull ⊤ : Set m.atom.ogp) \ m.atom.ogp.interior (.Iic Rr) = _
    exact hornSet_closure_eq_union (β := false) hd.ge false (hdim true) (hdim false) hp
  have hI : LowerSet.Iic L ⊓ m.atom.ogp.bdry ⊤ true = m.atom.ogp.boundary (.Iic L) 0 false :=
    inter_bdry_eq_boundary_of_dimension_eq_two (β := false) hd false (hdim true) hp
  obtain ⟨s, hsmin, hs⟩ := exists_boundary_zero_eq_Iic m.atom.isMolecule false
  obtain ⟨t, htmin, ht⟩ := exists_boundary_zero_eq_Iic m.atom.isMolecule true
  have hLs : m.atom.ogp.boundary (.Iic L) 0 false = .Iic s := by
    rw [← hs, ← boundary_bdry_zero m.atom (by omega) false false]
    exact (hp.boundary_eq_of_le_cond false hgB hgA (i := 0) (by omega)).symm
  have hRrt : m.atom.ogp.boundary (.Iic Rr) 0 true = .Iic t := by
    rw [← ht, ← boundary_bdry_zero m.atom (by omega) false true]
    exact (hp.boundary_eq_of_le_cond true hgA hgB (i := 0) (by omega)).symm
  have hTtop : m.atom.ogp.boundary (.Iic m.atom.top) 0 true = .Iic t := by
    rw [m.atom.Iic_top, ht]
  obtain ⟨hLRr, hne⟩ := invertorTopElt_ne_of_dimension_eq_one V true hV h1
  have hLtop : L ≠ m.atom.top := hne false
  have hRrtop : Rr ≠ m.atom.top := hne true
  have hmark : ∀ b, b ∈ m.marking ↔ b = L := fun _ => Set.mem_singleton_iff
  let R : m.atom.ogp → m.atom.ogp → Prop := fun a b =>
    outputRel m.atom.ogp a b ∨ b ∈ m.marking ∧ grade ℕ b = 1
  have hRt : ∀ a b, R a b ↔
      outputRel m.atom.ogp a b ∨ b ∈ m.targetMarking ∧ grade ℕ b = 1 :=
    fun _ _ => or_congr_right (mem_targetMarking_invertorMarkedHorn_iff V true hV h1).symm
  have hQw : ∀ y ∈ (m.hornSet : Set m.atom.ogp), y < m.atom.top :=
    fun y hy => lt_of_le_of_ne (m.atom.le_top y) ((mem_hornSet_iff_ne_and_ne m).1 hy).2
  let R' : m.atom.ogp → m.atom.ogp → Prop := fun a b => R a b ∧ b ≠ m.atom.top
  have hR₂ : ∀ a, R' a m.atom.top → a = m.atom.top := fun _ h => absurd rfl h.2
  have hLw : ∀ a ∈ ((LowerSet.Iic L : LowerSet m.atom.ogp) : Set m.atom.ogp), a ≤ m.atom.top :=
    fun a _ => m.atom.le_top a
  have hwL : m.atom.top ∉ ((LowerSet.Iic L : LowerSet m.atom.ogp) : Set m.atom.ogp) := fun h =>
    lt_irrefl _ (hQw _ (by rw [hQ]; exact LowerSet.mem_sup_iff.2 (Or.inl h)))
  have hwN : m.atom.top ∉ (m.atom.ogp.bdry ⊤ true : Set m.atom.ogp) := fun h =>
    lt_irrefl _ (hQw _ (by rw [hQ]; exact LowerSet.mem_sup_iff.2 (Or.inr h)))
  have hLL : L ∈ ((LowerSet.Iic L : LowerSet m.atom.ogp) : Set m.atom.ogp) :=
    LowerSet.mem_Iic_iff.2 le_rfl
  have hsL : s ∈ ((LowerSet.Iic L : LowerSet m.atom.ogp) : Set m.atom.ogp) :=
    boundary_le _ 0 false (hLs ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  have htN : t ∈ m.atom.ogp.boundary (m.atom.ogp.bdry ⊤ true) 0 true := by
    rw [boundary_bdry_zero m.atom (by omega), ht]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  have := weakEquivalence_coneBase_of_le R'
    (Λ := ((LowerSet.Iic L : LowerSet m.atom.ogp) : Set m.atom.ogp)) (u := L)
    (w := m.atom.top) (fun a ha => LowerSet.mem_Iic_iff.1 ha) hLL hLw hwL hR₂
  have := weakEquivalence_coneBase_of_edge R' hsL hLL (LowerSet.mem_Iic_iff.1 hsL)
    ⟨Or.inr ⟨(hmark L).2 rfl, (hdim false).trans (by omega)⟩, hLtop⟩ hLw hwL hR₂
  have := weakEquivalence_coneBase_of_isMoleculeIn R' (w := m.atom.top)
    (fun _ _ _ hb h => ⟨Or.inl h, hb.ne⟩) hR₂ (m.isMoleculeIn_bdry true)
    (fun y hy => hQw y (by rw [hQ]; exact LowerSet.mem_sup_iff.2 (Or.inr hy))) htN
  have hVWa : ((LowerSet.Iic L : LowerSet m.atom.ogp) : Set m.atom.ogp) ∩
      (m.atom.ogp.bdry ⊤ true : Set m.atom.ogp) = {s} := by
    rw [← LowerSet.coe_inf, hI, hLs, LowerSet.coe_Iic, hsmin.Iic_eq]
  have := weakEquivalence_coneBase_union_of_inter_eq R' hsL
    (boundary_le _ 0 true htN) hVWa hwL hwN mem_or_mem_of_le_or_le
  have hQ' : (((LowerSet.Iic L : LowerSet m.atom.ogp) : Set m.atom.ogp) ∪
      (m.atom.ogp.bdry ⊤ true : Set m.atom.ogp)) = (m.hornSet : Set m.atom.ogp) := by
    rw [hQ, LowerSet.coe_sup]
  have := weakEquivalence_coneBase_congr R' (w := m.atom.top) hQ'
    (Or.inr (boundary_le _ 0 true htN))
  have hTt : m.atom.ogp.boundary (.Iic t) 0 true = .Iic t := boundary_Iic_of_isMin htmin 0 true
  have hout : outputRel m.atom.ogp m.face m.atom.top := hRrt.trans hTtop.symm
  refine weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_rel m (fun _ _ => Iff.rfl) hRt
    (weakEquivalence_markedSubcomplexMap_chainSubcomplex_horn R (x := m.face) m.atom.le_top
      (fun a => mem_hornSet_iff_ne_and_ne m) (fun b hb => eq_or_eq_top_of_face_le m hb) ?_
      (hQ' ▸ Or.inr (boundary_le _ 0 true htN))
      (Or.inl (hTt.trans hTtop.symm)) (fun a haQ ha => ?_) (Or.inl hout) (fun a _ ha => ?_))
  · exact hRrtop
  · rcases ha with ha | ⟨hm, -⟩
    · have hta : t ∈ m.atom.ogp.boundary (.Iic a) 0 true := by
        rw [ha, hTtop]
        exact LowerSet.mem_Iic_iff.2 le_rfl
      exact ⟨a, haQ, LowerSet.mem_Iic_iff.1 (boundary_le _ 0 true hta),
        Or.inl (Or.inl (hTt.trans (ha.trans hTtop).symm)), Or.inl ha, le_refl a, Or.inr rfl⟩
    · exact absurd ((hmark _).1 hm).symm hLtop
  · rcases ha with ha | ⟨hm, -⟩
    · exact Or.inl (ha.trans hout)
    · exact absurd ((hmark _).1 hm).symm hLRr

private theorem weakEquivalence_markedFaceNerve_map_invertorMarkedHorn_false_of_dimension_eq_one
    (hV : 0 < V.dimension) (h1 : V.dimension = 1) :
    WeakEquivalence (markedFaceNerve.{u}.map
      (markedHornInclusion (Shape.invertorMarkedHorn V false hV))) := by
  let m := Shape.invertorMarkedHorn V false hV
  let L : m.atom.ogp := Shape.invertorTopElt V false hV (some false)
  let Rr : m.atom.ogp := Shape.invertorTopElt V false hV (some true)
  have hd : m.atom.dimension = 2 := by
    change (Shape.invertorAtom V false hV).dimension = 2
    rw [Shape.dimension_invertorAtom, h1]
  have hdim (β : Bool) : grade ℕ (Shape.invertorTopElt V false hV (some β)) =
      m.atom.dimension - 1 := by
    rw [hd]
    exact (Shape.dim_invertorTopElt_some V false hV β).trans h1
  have hdL : grade ℕ L = 1 := (hdim false).trans (by omega)
  have hdRr : grade ℕ Rr = 1 := (hdim true).trans (by omega)
  have hp : m.atom.ogp.IsPastingIn (m.atom.dimension - 2) (.Iic L) (.Iic Rr)
      (m.atom.ogp.bdry ⊤ true) :=
    Shape.isPastingIn_closure_invertorTopElt V false hV
  have hgA := IsMoleculeIn.isGlobular (m.atom.isRDC L)
  have hgB := IsMoleculeIn.isGlobular (m.atom.isRDC Rr)
  have hQ : (m.hornSet : Set m.atom.ogp) =
      ((LowerSet.Iic Rr ⊔ m.atom.ogp.bdry ⊤ false : LowerSet m.atom.ogp) : Set m.atom.ogp) := by
    change (m.atom.ogp.bdryFull ⊤ : Set m.atom.ogp) \ m.atom.ogp.interior (.Iic L) = _
    exact hornSet_closure_eq_union (β := true) hd.ge true (hdim false) (hdim true) hp
  have hI : LowerSet.Iic Rr ⊓ m.atom.ogp.bdry ⊤ false = m.atom.ogp.boundary (.Iic Rr) 0 true :=
    inter_bdry_eq_boundary_of_dimension_eq_two (β := true) hd true (hdim false) hp
  obtain ⟨t, htmin, ht⟩ := exists_boundary_zero_eq_Iic m.atom.isMolecule true
  obtain ⟨v, hvmin, hv⟩ := exists_boundary_zero_eq_Iic (m.atom.isRDC L) true
  have hRrt : m.atom.ogp.boundary (.Iic Rr) 0 true = .Iic t := by
    rw [← ht, ← boundary_bdry_zero m.atom (by omega) true true]
    exact (hp.boundary_eq_of_le_cond true hgA hgB (i := 0) (by omega)).symm
  have hTtop : m.atom.ogp.boundary (.Iic m.atom.top) 0 true = .Iic t := by
    rw [m.atom.Iic_top, ht]
  have hTt : m.atom.ogp.boundary (.Iic t) 0 true = .Iic t := boundary_Iic_of_isMin htmin 0 true
  have hTv : m.atom.ogp.boundary (.Iic v) 0 true = .Iic v := boundary_Iic_of_isMin hvmin 0 true
  have hvL : v ≤ L := LowerSet.mem_Iic_iff.1
    (boundary_le _ 0 true (hv ▸ LowerSet.mem_Iic_iff.2 le_rfl))
  have hvRr : v ≤ Rr := by
    have h₀ := hp.inf_eq_output
    rw [(by omega : m.atom.dimension - 2 = 0)] at h₀
    have h := (congrArg (v ∈ ·) h₀).mpr (hv ▸ LowerSet.mem_Iic_iff.2 le_rfl)
    exact LowerSet.mem_Iic_iff.1 (LowerSet.mem_inf_iff.1 h).2
  have htRr : t ∈ ((LowerSet.Iic Rr : LowerSet m.atom.ogp) : Set m.atom.ogp) :=
    boundary_le _ 0 true (hRrt ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  obtain ⟨hLRr, hne⟩ := invertorTopElt_ne_of_dimension_eq_one V false hV h1
  have hLtop : L ≠ m.atom.top := hne false
  have hRrtop : Rr ≠ m.atom.top := hne true
  have hmark : ∀ b, b ∈ m.marking ↔ b = Rr := fun _ => Set.mem_singleton_iff
  let R : m.atom.ogp → m.atom.ogp → Prop := fun a b =>
    outputRel m.atom.ogp a b ∨ b ∈ m.marking ∧ grade ℕ b = 1
  have hRt : ∀ a b, R a b ↔
      outputRel m.atom.ogp a b ∨ b ∈ m.targetMarking ∧ grade ℕ b = 1 :=
    fun _ _ => or_congr_right (mem_targetMarking_invertorMarkedHorn_iff V false hV h1).symm
  have hQw : ∀ y ∈ (m.hornSet : Set m.atom.ogp), y < m.atom.top :=
    fun y hy => lt_of_le_of_ne (m.atom.le_top y) ((mem_hornSet_iff_ne_and_ne m).1 hy).2
  let R' : m.atom.ogp → m.atom.ogp → Prop := fun a b => R a b ∧ b ≠ m.atom.top
  have hR₁ : ∀ a b, a ≤ b → b < m.atom.top → outputRel m.atom.ogp a b → R' a b :=
    fun _ _ _ hb h => ⟨Or.inl h, hb.ne⟩
  have hR₂ : ∀ a, R' a m.atom.top → a = m.atom.top := fun _ h => absurd rfl h.2
  have hwRr : m.atom.top ∉ ((LowerSet.Iic Rr : LowerSet m.atom.ogp) : Set m.atom.ogp) := fun h =>
    lt_irrefl _ (hQw _ (by rw [hQ]; exact LowerSet.mem_sup_iff.2 (Or.inl h)))
  have hwN : m.atom.top ∉ (m.atom.ogp.bdry ⊤ false : Set m.atom.ogp) := fun h =>
    lt_irrefl _ (hQw _ (by rw [hQ]; exact LowerSet.mem_sup_iff.2 (Or.inr h)))
  have htN : t ∈ m.atom.ogp.boundary (m.atom.ogp.bdry ⊤ false) 0 true := by
    rw [boundary_bdry_zero m.atom (by omega), ht]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  have htN' : t ∈ m.atom.ogp.bdry ⊤ false := boundary_le _ 0 true htN
  have := weakEquivalence_coneBase_of_isMoleculeIn R' (w := m.atom.top) hR₁ hR₂
    (m.atom.isRDC Rr) (fun y hy => hQw y (by rw [hQ]; exact LowerSet.mem_sup_iff.2 (Or.inl hy)))
    (hRrt ▸ LowerSet.mem_Iic_iff.2 le_rfl)
  have := weakEquivalence_coneBase_of_isMoleculeIn R' (w := m.atom.top) hR₁ hR₂
    (m.isMoleculeIn_bdry false)
    (fun y hy => hQw y (by rw [hQ]; exact LowerSet.mem_sup_iff.2 (Or.inr hy))) htN
  have := weakEquivalence_coneBase_singleton R' (w := m.atom.top) t
  have hVW : ({t} : Set m.atom.ogp) = ((LowerSet.Iic Rr : LowerSet m.atom.ogp) : Set m.atom.ogp) ∩
      (m.atom.ogp.bdry ⊤ false : Set m.atom.ogp) := by
    rw [← LowerSet.coe_inf, hI, hRrt, LowerSet.coe_Iic, htmin.Iic_eq]
  have := weakEquivalence_coneBase_congr R' (w := m.atom.top) hVW (Set.mem_singleton t)
  have := weakEquivalence_coneBase_union R' (w := m.atom.top)
    (V := ((LowerSet.Iic Rr : LowerSet m.atom.ogp) : Set m.atom.ogp)) htRr htN' hwRr hwN
    mem_or_mem_of_le_or_le
  have hQ' : (((LowerSet.Iic Rr : LowerSet m.atom.ogp) : Set m.atom.ogp) ∪
      (m.atom.ogp.bdry ⊤ false : Set m.atom.ogp)) = (m.hornSet : Set m.atom.ogp) := by
    rw [hQ, LowerSet.coe_sup]
  have := weakEquivalence_coneBase_congr R' (w := m.atom.top) hQ' (Or.inl htRr)
  let R₁ : m.atom.ogp → m.atom.ogp → Prop := fun a b =>
    R a b ∨ b = m.atom.top ∧ a = v
  let R₂ : m.atom.ogp → m.atom.ogp → Prop := fun a b =>
    R a b ∨ b = m.atom.top ∧ (a = v ∨ a = L)
  have hRR₁ : ∀ a b, R a b → R₁ a b := fun _ _ h => Or.inl h
  have hR₁R₂ : ∀ a b, R₁ a b → R₂ a b := by
    rintro a b (h | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, Or.inl rfl⟩
  have hRR₂ : ∀ a b, R a b → R₂ a b := fun _ _ h => Or.inl h
  have hRrT : outputRel m.atom.ogp Rr m.atom.top := hRrt.trans hTtop.symm
  have hvRrR : R v Rr := Or.inr ⟨(hmark Rr).2 rfl, hdRr⟩
  have hvL' : outputRel m.atom.ogp v L := hTv.trans hv.symm
  have : WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hRR₁)
      (chainSubcomplex (Set.univ : Set m.atom.ogp))) := by
    refine weakEquivalence_markedSubcomplexRemark_chainSubcomplex hRR₁ _ fun a _ b _ _ h => ?_
    rcases h with h | ⟨rfl, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨Rr, Set.mem_univ _, Or.inr (Or.inl ⟨hvRr, m.atom.le_top Rr, Or.inl hvRrR,
        Or.inl (Or.inl hRrT)⟩)⟩
  have : WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hR₁R₂)
      (chainSubcomplex (Set.univ : Set m.atom.ogp))) := by
    refine weakEquivalence_markedSubcomplexRemark_chainSubcomplex hR₁R₂ _ fun a _ b _ _ h => ?_
    rcases h with h | ⟨rfl, rfl | rfl⟩
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr ⟨v, Set.mem_univ _, Or.inl ⟨hvL, Or.inl (Or.inl (Or.inl hvL')),
        Or.inl (Or.inr ⟨rfl, rfl⟩)⟩⟩
  have : WeakEquivalence (markedSubcomplexRemark (edgeSet_mono hRR₂)
      (chainSubcomplex (Set.univ : Set m.atom.ogp))) := by
    have e : markedSubcomplexRemark (edgeSet_mono hRR₂)
        (chainSubcomplex (Set.univ : Set m.atom.ogp)) =
        markedSubcomplexRemark (edgeSet_mono hRR₁) (chainSubcomplex Set.univ) ≫
          markedSubcomplexRemark (edgeSet_mono hR₁R₂) (chainSubcomplex Set.univ) :=
      MarkedPresheaf.hom_ext rfl
    rw [e]
    infer_instance
  refine weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_rel m (fun _ _ => Iff.rfl) hRt
    (weakEquivalence_markedSubcomplexMap_chainSubcomplex_horn_of_le R (x := m.face) hRR₂ ?_
      m.atom.le_top (fun a => mem_hornSet_iff_ne_and_ne m)
      (fun b hb => eq_or_eq_top_of_face_le m hb) hLtop (hQ' ▸ Or.inl htRr)
      (Or.inl (Or.inl (hTt.trans hTtop.symm))) (fun a haQ ha => ?_) (Or.inr ⟨rfl, Or.inr rfl⟩)
      (fun a hal ha => ?_))
  · rintro a b (h | ⟨rfl, -⟩) hb
    · exact h
    · exact absurd rfl hb
  · rcases ha with (ha | ⟨hm, -⟩) | ⟨-, rfl | rfl⟩
    · have hta : t ∈ m.atom.ogp.boundary (.Iic a) 0 true := by
        rw [ha, hTtop]
        exact LowerSet.mem_Iic_iff.2 le_rfl
      exact ⟨a, haQ, LowerSet.mem_Iic_iff.1 (boundary_le _ 0 true hta),
        Or.inl (Or.inl (Or.inl (hTt.trans (ha.trans hTtop).symm))), Or.inl (Or.inl ha),
        le_refl a, Or.inr rfl⟩
    · exact absurd ((hmark _).1 hm).symm hRrtop
    · exact ⟨Rr, (mem_hornSet_iff_ne_and_ne m).2 ⟨hLRr.symm, hRrtop⟩,
        LowerSet.mem_Iic_iff.1 htRr, Or.inl (Or.inl (Or.inl (hTt.trans hRrt.symm))),
        Or.inl (Or.inl hRrT), hvRr, Or.inl (Or.inl hvRrR)⟩
    · exact absurd rfl ((mem_hornSet_iff_ne_and_ne m).1 haQ).1
  · rcases ha with (ha | ⟨hm, -⟩) | ⟨h, -⟩
    · refine Or.inr ⟨rfl, ?_⟩
      rcases eq_or_lt_of_le hal with rfl | hlt
      · exact Or.inr rfl
      · have hd₀ : grade ℕ a = 0 := by
          have : grade ℕ a < grade ℕ L := grade_strictMono hlt
          omega
        have h' := (boundary_Iic_of_isMin (grade_eq_zero_iff.1 hd₀) 0 true).symm.trans (ha.trans hv)
        exact Or.inl (LowerSet.Iic_inj.1 h')
    · exact absurd ((hmark _).1 hm) hLRr
    · exact absurd h hLtop

end InvertorArrow

section InvertorHorn

theorem weakEquivalence_markedFaceNerve_map_invertorMarkedHorn (V : Shape.Atom) (ε : Bool)
    (hV : 0 < V.dimension) :
    WeakEquivalence (markedFaceNerve.{u}.map
      (markedHornInclusion (Shape.invertorMarkedHorn V ε hV))) := by
  by_cases h1 : V.dimension = 1
  · cases ε
    · exact weakEquivalence_markedFaceNerve_map_invertorMarkedHorn_false_of_dimension_eq_one V hV h1
    · exact weakEquivalence_markedFaceNerve_map_invertorMarkedHorn_true_of_dimension_eq_one V hV h1
  · exact weakEquivalence_markedFaceNerve_map_invertorMarkedHorn_of_two_le V ε hV (by omega)

end InvertorHorn

section Marking

open Opposite

theorem isIso_markedFaceNerve_map_of_isIso_forget_map {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y)
    [hfi : IsIso (MarkedPresheaf.forget.map f)]
    (h : ∀ (V : Shape.Atom) (y : Y.underlying.obj (op V)), y ∈ Y.marked V →
      V.dimension = 1 → ∃ x ∈ X.marked V, (MarkedPresheaf.forget.map f).app _ x = y) :
    IsIso (markedFaceNerve.map f) := by
  refine isIso_of_coyoneda_map_bijective _ fun T => ?_
  have key : (fun (x : markedFaceNerve.obj Y ⟶ T) => markedFaceNerve.map f ≫ x) =
      (markedFaceNerveAdjunction.homEquiv X T).symm ∘ (fun k => f ≫ k) ∘
        markedFaceNerveAdjunction.homEquiv Y T := by
    funext x
    simp only [Function.comp_apply, Adjunction.homEquiv_naturality_left_symm,
      Equiv.symm_apply_apply]
  rw [key]
  refine (markedFaceNerveAdjunction.homEquiv X T).symm.bijective.comp
    (Function.Bijective.comp ?_ (markedFaceNerveAdjunction.homEquiv Y T).bijective)
  have hf : Epi (MarkedPresheaf.forget.map f) := inferInstance
  have : Epi f := MarkedPresheaf.forget.epi_of_epi_map hf
  refine ⟨fun k k' hk => (cancel_epi f).1 hk, fun k => ?_⟩
  refine ⟨MarkedPresheaf.homMk (@CategoryTheory.inv _ _ _ _ (MarkedPresheaf.forget.map f) hfi ≫
    MarkedPresheaf.forget.map k)
    fun V y hy => ?_, MarkedPresheaf.hom_ext ?_⟩
  · by_cases hV : V.dimension = 1
    · obtain ⟨x, hx, rfl⟩ := h V y hy hV
      have e : (inv (MarkedPresheaf.forget.map f) ≫ MarkedPresheaf.forget.map k).app _
          ((MarkedPresheaf.forget.map f).app _ x) = (MarkedPresheaf.forget.map k).app _ x :=
        ConcreteCategory.congr_hom (congr_app (IsIso.hom_inv_id_assoc
          (MarkedPresheaf.forget.map f) (MarkedPresheaf.forget.map k)) (op V)) x
      exact (congrArg (· ∈ _) e).mpr (MarkedPresheaf.map_mem_marked k hx)
    · have hpos : 0 < V.dimension := Y.markable V y hy
      have := isIso_markedFaceNerveSite_map_toSelf V hpos hV
      let z : markedFaceNerveSite.obj ((MarkedSite.unmarked atomMarking).obj V) ⟶ T :=
        (@CategoryTheory.inv _ _ _ _ (MarkedPresheaf.forget.map f) hfi ≫
          MarkedPresheaf.forget.map k).app (op V) y
      exact ⟨hpos, inv (markedFaceNerveSite.map
        (MarkedSite.toSelf (MarkedSite.marked V hpos))) ≫ z,
        IsIso.hom_inv_id_assoc (markedFaceNerveSite.map
          (MarkedSite.toSelf (MarkedSite.marked V hpos))) z⟩
  · exact (MarkedPresheaf.forget.map_comp _ _).trans (IsIso.hom_inv_id_assoc _ _)

end Marking

section Marking

open Opposite

theorem isIso_markedFaceNerve_map_markingInclusion (U : Shape.Atom) (hU : 1 < U.dimension) :
    IsIso (markedFaceNerve.{u}.map (MarkedDiagSet.markingInclusion U (by omega))) := by
  have : CategoryTheory.IsIso (MarkedPresheaf.forget.map
      (MarkedDiagSet.markingInclusion U (by omega))) :=
    inferInstanceAs (CategoryTheory.IsIso (𝟙 _))
  refine isIso_markedFaceNerve_map_of_isIso_forget_map _ fun V y hy hV => ⟨y, ?_, rfl⟩
  rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hy with hy | hy
  · exact (MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V y).2 hy
  · have h' : V.dimension = U.dimension :=
      Shape.Atom.dimension_eq_of_iso (asIso (y.down : V ⟶ U))
    omega

private theorem isIso_markedFaceNerve_map_markedAboveMap_invertorPair (U : Shape.Atom)
    (hU : 0 < U.dimension) (h2 : 2 ≤ U.dimension) :
    IsIso (markedFaceNerve.{u}.map (MarkedDiagSet.markedAboveMap (invertorPair U hU)
      (Nat.sub_le U.dimension 1))) := by
  have : CategoryTheory.IsIso (MarkedPresheaf.forget.map (MarkedDiagSet.markedAboveMap
      (invertorPair U hU) (Nat.sub_le U.dimension 1))) :=
    inferInstanceAs (CategoryTheory.IsIso (𝟙 _))
  refine isIso_markedFaceNerve_map_of_isIso_forget_map _ fun V y hy hV => ⟨y, ?_, rfl⟩
  rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hy with hy | hy
  · exact (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inl hy)
  · have h' : U.dimension - 1 < V.dimension := hy
    omega

end Marking

section Triangle

open Simplicial Opposite SSet SimplicialObject.Truncated

variable {C : Type} [PartialOrder C] {F : SSet.{u}}

private abbrev edgeOfLE {a b : C} (h : a ≤ b) : (nerve (ULift.{u} C)) _⦋1⦌ :=
  ComposableArrows.mk₁ (homOfLE (ULift.up_le.2 h))

private def nerveEdge {a b : C} (h : a ≤ b) :
    Edge (X := nerve (ULift.{u} C)) (ComposableArrows.mk₀ (ULift.up a))
      (ComposableArrows.mk₀ (ULift.up b)) :=
  Edge.mk (ComposableArrows.mk₁ (homOfLE (ULift.up_le.2 h)))
    (ComposableArrows.ext₀ rfl) (ComposableArrows.ext₀ rfl)

private def nerveCompStruct {a b c : C} (hab : a ≤ b) (hbc : b ≤ c) :
    Edge.CompStruct (nerveEdge.{u} hab) (nerveEdge hbc) (nerveEdge (hab.trans hbc)) :=
  Edge.CompStruct.mk
    (ComposableArrows.mk₂ (homOfLE (ULift.up_le.2 hab)) (homOfLE (ULift.up_le.2 hbc)))
    (nerve.ext_of_isThin (funext fun i => by fin_cases i <;> rfl))
    (nerve.ext_of_isThin (funext fun i => by fin_cases i <;> rfl))
    (nerve.ext_of_isThin (funext fun i => by fin_cases i <;> rfl))

private abbrev hoEdge (G : nerve (ULift.{u} C) ⟶ F) {a b : C} (h : a ≤ b) :=
  Truncated.HomotopyCategory.homMk (V := (truncation 2).obj F) ((nerveEdge h).map G).toTruncated

private theorem hoEdge_comp (G : nerve (ULift.{u} C) ⟶ F) {a b c : C} (hab : a ≤ b)
    (hbc : b ≤ c) :
    hoEdge G hab ≫ hoEdge G hbc = hoEdge G (hab.trans hbc) :=
  Truncated.HomotopyCategory.homMk_comp_homMk ((nerveCompStruct hab hbc).map G).toTruncated

private theorem isIso_hoEdge_iff [F.Quasicategory] (G : nerve (ULift.{u} C) ⟶ F) {a b : C}
    (h : a ≤ b) : IsIso (hoEdge G h) ↔ Nonempty (Edge.mk' (G.app _ (edgeOfLE h))).InvStruct := by
  exact (isIso_homMk_iff ((nerveEdge h).map G)).trans
    ⟨fun ⟨I⟩ => ⟨I.ofEq rfl⟩, fun ⟨I⟩ => ⟨I.ofEq rfl⟩⟩

private theorem prop_homMk_iff {V : Truncated.{u} 2}
    (P : ∀ {x y : V.HomotopyCategory}, (x ⟶ y) → Prop) {x₀ x₁ y₀ y₁ : V _⦋0⦌₂}
    (e : Truncated.Edge x₀ x₁) (e' : Truncated.Edge y₀ y₁) (h : e.edge = e'.edge) :
    P (Truncated.HomotopyCategory.homMk e) ↔ P (Truncated.HomotopyCategory.homMk e') := by
  obtain rfl : x₀ = y₀ := by rw [← e.src_eq, ← e'.src_eq, h]
  obtain rfl : x₁ = y₁ := by rw [← e.tgt_eq, ← e'.tgt_eq, h]
  obtain rfl : e = e' := by cases e; cases e'; cases h; rfl
  rfl

private theorem prop_hoEdge_iff (P : ∀ {x y : ((truncation 2).obj F).HomotopyCategory},
      (x ⟶ y) → Prop) {C' : Type} [PartialOrder C'] (G : nerve (ULift.{u} C) ⟶ F)
    (G' : nerve (ULift.{u} C') ⟶ F) {a b : C} {a' b' : C'} (h : a ≤ b) (h' : a' ≤ b')
    (he : G.app (op ⦋1⦌) (edgeOfLE h) = G'.app (op ⦋1⦌) (edgeOfLE h')) :
    P (hoEdge G h) ↔ P (hoEdge G' h') :=
  prop_homMk_iff P _ _ he

private theorem isSplitMono_and_isSplitEpi_of_triangles {𝒞 : Type*} [Category 𝒞]
    {S M T L R K W : 𝒞} {sl : S ⟶ L} {ml : M ⟶ L} {mr : M ⟶ R} {lw : L ⟶ W} {rw : R ⟶ W}
    {sk : S ⟶ K} {tk : T ⟶ K} {kw : K ⟶ W} {sw : S ⟶ W} {tw : T ⟶ W} {mw : M ⟶ W}
    (h₁ : sl ≫ lw = sw) (h₂ : sk ≫ kw = sw) (h₃ : tk ≫ kw = tw) (h₄ : ml ≫ lw = mw)
    (h₅ : mr ≫ rw = mw) [IsIso ml] [IsIso rw] [IsIso tw] [IsIso sk] [IsIso tk] :
    IsSplitMono sl ∧ IsSplitEpi mr ∧ (IsIso sl ↔ IsIso mr) := by
  have : IsIso (tk ≫ kw) := h₃ ▸ inferInstance
  have : IsIso kw := IsIso.of_isIso_comp_left tk kw
  have : IsIso sw := h₂ ▸ inferInstance
  refine ⟨IsSplitMono.mk' ⟨lw ≫ inv sw, by rw [← Category.assoc, h₁, IsIso.hom_inv_id]⟩,
    IsSplitEpi.mk' ⟨rw ≫ inv sw ≫ sl ≫ inv ml, ?_⟩, ⟨fun _ => ?_, fun _ => ?_⟩⟩
  · have hm : inv ml ≫ mr = lw ≫ inv rw := by
      rw [IsIso.inv_comp_eq, ← Category.assoc, h₄, ← h₅, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]
    rw [Category.assoc, Category.assoc, Category.assoc, hm, ← Category.assoc sl,
      h₁, ← Category.assoc (inv sw), IsIso.inv_hom_id, Category.id_comp, IsIso.hom_inv_id]
  · have : IsIso (sl ≫ lw) := h₁ ▸ inferInstance
    have : IsIso lw := IsIso.of_isIso_comp_left sl lw
    have : IsIso mw := h₄ ▸ inferInstance
    have : IsIso (mr ≫ rw) := h₅ ▸ inferInstance
    exact IsIso.of_isIso_comp_right mr rw
  · have : IsIso mw := h₅ ▸ inferInstance
    have : IsIso (ml ≫ lw) := h₄ ▸ inferInstance
    have : IsIso lw := IsIso.of_isIso_comp_left ml lw
    have : IsIso (sl ≫ lw) := h₁ ▸ inferInstance
    exact IsIso.of_isIso_comp_right sl lw

private theorem isIso_hoEdge_of_eq [F.Quasicategory] (G : nerve (ULift.{u} C) ⟶ F) {a b : C}
    (h : a ≤ b) (hab : a = b) : IsIso (hoEdge G h) := by
  subst hab
  refine (isIso_hoEdge_iff G h).2 ?_
  have e : edgeOfLE h =
      (nerve (ULift.{u} C)).σ 0
        (ComposableArrows.mk₀ (ULift.up a) : (nerve (ULift.{u} C)) _⦋0⦌) :=
    nerve.ext_of_isThin (n := op ⦋1⦌) (funext fun i => by fin_cases i <;> rfl)
  have hn := SSet.σ_naturality_apply G 0
    (ComposableArrows.mk₀ (ULift.up a) : (nerve (ULift.{u} C)) _⦋0⦌)
  rw [e, hn]
  exact ⟨(Edge.InvStruct.invStructId _).ofEq rfl⟩

private theorem edgeOfLE_congr {a b a' b' : C} (h : a ≤ b) (h' : a' ≤ b') (ha : a = a')
    (hb : b = b') : edgeOfLE.{u} h = edgeOfLE h' := by
  subst ha hb
  rfl

private theorem triangle_hoEdge (G : nerve (ULift.{u} C) ⟶ F) {s m t l r k w : C} (hsl : s ≤ l)
    (hml : m ≤ l) (hmr : m ≤ r) (hsk : s ≤ k) (htk : t ≤ k) (hlw : l ≤ w) (hrw : r ≤ w)
    (hkw : k ≤ w)
    [IsIso (hoEdge G hml)] [IsIso (hoEdge G hrw)] [IsIso (hoEdge G (htk.trans hkw))]
    [IsIso (hoEdge G hsk)] [IsIso (hoEdge G htk)] :
    IsSplitMono (hoEdge G hsl) ∧ IsSplitEpi (hoEdge G hmr) ∧
      (IsIso (hoEdge G hsl) ↔ IsIso (hoEdge G hmr)) :=
  isSplitMono_and_isSplitEpi_of_triangles (hoEdge_comp G hsl hlw) (hoEdge_comp G hsk hkw)
    (hoEdge_comp G htk hkw) (hoEdge_comp G hml hlw) (hoEdge_comp G hmr hrw)

end Triangle

section RealizeCells

open Opposite

variable {Y : MarkedDiagSet.{u}}

private noncomputable def markedFaceNerveCounit (Y : MarkedDiagSet.{u}) :
    faceNerve.obj Y.underlying ⟶ markedFaceNerve.obj Y :=
  markedFaceNerve.map ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app Y)

private noncomputable def realizeFaceNerve {P : RDCpx.{0}}
    (Φ : realize.obj P ⟶ Y.underlying) :
    MarkedPresheaf.forget.obj (rdcFaceNerve.obj P) ⟶
      MarkedPresheaf.forget.obj (markedFaceNerve.obj Y) :=
  MarkedPresheaf.forget.map (realizeCompFaceNerveIso.inv.app P ≫ faceNerve.map Φ ≫
    markedFaceNerveCounit Y)

private theorem realizeFaceNerve_comp {P Q : RDCpx.{0}} (φ : P ⟶ Q)
    (Φ : realize.obj Q ⟶ Y.underlying) :
    realizeFaceNerve (realize.map φ ≫ Φ) =
      MarkedPresheaf.forget.map (rdcFaceNerve.map φ) ≫ realizeFaceNerve Φ := by
  have h := realizeCompFaceNerveIso.inv.naturality φ
  rw [Functor.comp_map] at h
  rw [realizeFaceNerve, realizeFaceNerve, ← Functor.map_comp]
  refine congrArg MarkedPresheaf.forget.map ?_
  rw [faceNerve.map_comp, ← Category.assoc (rdcFaceNerve.map φ), h]
  simp only [Category.assoc]

private theorem realizeFaceNerve_ofCell {W : Shape.Atom} (c : Y.underlying.obj (op W)) :
    realizeFaceNerve (PastingDiagram.ofCell c).map =
      MarkedPresheaf.forget.map (markedFaceNerveCell
        (x := (MarkedSite.unmarked atomMarking).obj W) c) := by
  let e : uliftYoneda.{u}.obj W ⟶ realize.obj (Shape.atomToRDCpx.obj W) :=
    uliftYonedaEquiv.symm ⟨𝟙 _⟩
  have h₁ : e ≫ (realizeAtomIso W).hom = 𝟙 _ := by
    ext ⟨T⟩ g
    rfl
  have h₂ : realizeCompFaceNerveIso.inv.app (Shape.atomToRDCpx.obj W) =
      yonedaCompFaceNerveIso.inv.app W ≫ faceNerve.map e := by
    have h := faceNerve_map_comp_realizeCompFaceNerveIso_hom_app (𝟙 (Shape.atomToRDCpx.obj W))
    rw [rdcFaceNerve.map_id, ← Category.assoc] at h
    exact ((Iso.comp_hom_eq_id _).1 h).symm
  have h₃ : faceNerve.map e ≫ faceNerve.map (PastingDiagram.ofCell c).map =
      faceNerve.map (uliftYonedaEquiv.symm c) := by
    refine (faceNerve.map_comp e (PastingDiagram.ofCell c).map).symm.trans
      (congrArg faceNerve.map ?_)
    change e ≫ (realizeAtomIso W).hom ≫ uliftYonedaEquiv.symm c = _
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ uliftYonedaEquiv.symm c) h₁).trans
      (Category.id_comp _))
  change MarkedPresheaf.forget.map (realizeCompFaceNerveIso.inv.app (Shape.atomToRDCpx.obj W) ≫
    faceNerve.map (PastingDiagram.ofCell c).map ≫ markedFaceNerveCounit Y) = _
  rw [h₂, markedFaceNerveCell_unmarked,
    Functor.map_comp _ (unmarkedCompMarkedFaceNerveSiteIso.hom.app W),
    forget_map_unmarkedCompMarkedFaceNerveSiteIso_hom_app]
  refine (congrArg MarkedPresheaf.forget.map ?_).trans (Category.id_comp _).symm
  rw [Category.assoc, ← Category.assoc (faceNerve.map _)]
  exact congrArg (fun k => yonedaCompFaceNerveIso.inv.app W ≫ k ≫ markedFaceNerveCounit Y) h₃

end RealizeCells

section InvertorPairArrow

open Simplicial Opposite PastingDiagram SSet

variable (U : Shape.Atom) (hU : 0 < U.dimension) (n : ℕ) {F : SSet.{u}}

private noncomputable abbrev invertorPairRealize
    (g : MarkedPresheaf.forget.obj (markedFaceNerve.obj
      (MarkedDiagSet.markedAbove (invertorPair U hU) n)) ⟶ F) {P : RDCpx.{0}}
    (Φ : realize.obj P ⟶ invertorPair U hU) : nerve (ULift.{u} P.obj.toOGP) ⟶ F :=
  realizeFaceNerve (Y := MarkedDiagSet.markedAbove (invertorPair U hU) n) Φ ≫ g

private theorem invertorPairRealize_comp
    (g : MarkedPresheaf.forget.obj (markedFaceNerve.obj
      (MarkedDiagSet.markedAbove (invertorPair U hU) n)) ⟶ F) {P Q : RDCpx.{0}}
    (φ : P ⟶ Q) (Φ : realize.obj Q ⟶ invertorPair U hU) {a b : P.obj.toOGP} (h : a ≤ b) :
    (invertorPairRealize U hU n g (realize.map φ ≫ Φ)).app _ (edgeOfLE h) =
      (invertorPairRealize U hU n g Φ).app _
        (edgeOfLE ((ConcreteCategory.hom φ.hom).isMap.monotone h)) := by
  have e := realizeFaceNerve_comp (Y := MarkedDiagSet.markedAbove (invertorPair U hU) n) φ Φ
  refine (congrArg (fun k => (k ≫ g).app _ (edgeOfLE h)) e).trans ?_
  have h' : (MarkedPresheaf.forget.map (rdcFaceNerve.map φ)).app _ (edgeOfLE h) =
      edgeOfLE ((ConcreteCategory.hom φ.hom).isMap.monotone h) :=
    nerve.ext_of_isThin (n := op ⦋1⦌) (funext fun i => by fin_cases i <;> rfl)
  exact congrArg (fun x => (realizeFaceNerve Φ ≫ g).app _ x) h'

private theorem invertorPairRealize_within
    (g : MarkedPresheaf.forget.obj (markedFaceNerve.obj
      (MarkedDiagSet.markedAbove (invertorPair U hU) n)) ⟶ F)
    {a m : PastingDiagram (invertorPair U hU)} (w : Within a m) {x y : a.shape.ogp} (h : x ≤ y) :
    (invertorPairRealize U hU n g m.map).app _ (edgeOfLE ((isMorphism w.emb).monotone h)) =
      (invertorPairRealize U hU n g a.map).app _ (edgeOfLE h) :=
  (invertorPairRealize_comp U hU n g (RDCpx.ofInclusion (P := a.shape.rdc) (Q := m.shape.rdc)
    w.emb) m.map h).symm.trans
    (congrArg (fun Φ => (invertorPairRealize U hU n g Φ).app _ (edgeOfLE h)) w.comm)

private theorem isSplitMono_and_isSplitEpi_of_withins [F.Quasicategory]
    (g : MarkedPresheaf.forget.obj (markedFaceNerve.obj
      (MarkedDiagSet.markedAbove (invertorPair U hU) n)) ⟶ F)
    (hM : ∀ (W : Shape.Atom) (c : (invertorPair U hU).obj (op W)) (a b : W.ogp)
      (hab : a ≤ b), outputRel W.ogp a b →
        IsIso (hoEdge (invertorPairRealize U hU n g (ofCell c).map) hab))
    {Z Wx Wy : Shape.Atom} {z : (invertorPair U hU).obj (op Z)}
    {x : (invertorPair U hU).obj (op Wx)} {y : (invertorPair U hU).obj (op Wy)}
    {P : MoleculeShape} {f : realize.obj P.rdc ⟶ invertorPair U hU}
    (wx : Within (ofCell x) (ofCell z)) (wy : Within (ofCell y) (ofCell z))
    (we : Within ⟨unitShape P, realize.map (cylProj P (P.ogp.bdryFull ⊤)) ≫ f⟩ (ofCell z))
    (hP : P.dimension = 0) {k : ℕ} (hk : k = 1) {α : Bool}
    (hp : Z.ogp.IsPastingIn (k - 1) wx.image wy.image (Z.ogp.boundary ⊤ k α))
    (he : we.image = Z.ogp.boundary ⊤ k (!α))
    {sx : Wx.ogp} (hsx : Wx.ogp.boundary ⊤ 0 false = .Iic sx)
    {sy : Wy.ogp} (hsy : Wy.ogp.boundary ⊤ 0 false = .Iic sy) :
    IsSplitMono (hoEdge (invertorPairRealize U hU n g (ofCell x).map) (Wx.le_top sx)) ∧
      IsSplitEpi (hoEdge (invertorPairRealize U hU n g (ofCell y).map) (Wy.le_top sy)) ∧
      (IsIso (hoEdge (invertorPairRealize U hU n g (ofCell x).map) (Wx.le_top sx)) ↔
        IsIso (hoEdge (invertorPairRealize U hU n g (ofCell y).map) (Wy.le_top sy))) := by
  subst hk
  let G := invertorPairRealize U hU n g (ofCell z).map
  have hglob (β γ : Bool) : Z.ogp.boundary (Z.ogp.boundary ⊤ 1 β) 0 γ = Z.ogp.boundary ⊤ 0 γ :=
    Z.isMolecule.isGlobular 0 1 Nat.one_pos γ β
  obtain ⟨tx, -, htx⟩ := exists_boundary_zero_eq_Iic Wx.isMolecule true
  obtain ⟨ty, -, hty⟩ := exists_boundary_zero_eq_Iic Wy.isMolecule true
  have hglue : wx.emb tx = wy.emb sy := by
    have h : OGP.map wx.emb (Wx.ogp.boundary ⊤ 0 true) =
        OGP.map wy.emb (Wy.ogp.boundary ⊤ 0 false) :=
      (wx.boundary_image 0 true).symm.trans
        (hp.inf_eq_output.symm.trans (hp.inf_eq_input.trans (wy.boundary_image 0 false)))
    rw [htx, hsy, map_Iic, map_Iic] at h
    exact LowerSet.Iic_inj.1 h
  let l := wx.emb Wx.top
  let r := wy.emb Wy.top
  let s := wx.emb sx
  let m := wy.emb sy
  let t := wy.emb ty
  have hsl : s ≤ l := (isMorphism wx.emb).monotone (Wx.le_top sx)
  have hml : m ≤ l := by
    change wy.emb sy ≤ wx.emb Wx.top
    rw [← hglue]
    exact (isMorphism wx.emb).monotone (Wx.le_top tx)
  have hmr : m ≤ r := (isMorphism wy.emb).monotone (Wy.le_top sy)
  have hZs : Z.ogp.boundary ⊤ 0 false = .Iic s := by
    have h : Z.ogp.boundary ⊤ 0 false = OGP.map wx.emb (Wx.ogp.boundary ⊤ 0 false) :=
      (hglob α false).symm.trans (hp.boundary_input.trans (wx.boundary_image 0 false))
    rw [h, hsx, map_Iic]
  have hZt : Z.ogp.boundary ⊤ 0 true = .Iic t := by
    have h : Z.ogp.boundary ⊤ 0 true = OGP.map wy.emb (Wy.ogp.boundary ⊤ 0 true) :=
      (hglob α true).symm.trans (hp.boundary_output.trans (wy.boundary_image 0 true))
    rw [h, hty, map_Iic]
  obtain ⟨top', htop⟩ := (isAtom_unitShape_of_dimension_eq_zero P hP).2
  have htop' : ∀ a, a ≤ top' := fun a => LowerSet.mem_Iic_iff.1 (htop ▸ LowerSet.mem_top)
  have hdeg : ∀ {a b : (unitShape P).ogp} (hab : a ≤ b),
      IsIso (hoEdge G ((isMorphism we.emb).monotone hab)) := by
    intro a b hab
    refine (prop_hoEdge_iff (fun f => IsIso f) _ _ _ _
      ((invertorPairRealize_within U hU n g we hab).trans
        (invertorPairRealize_comp U hU n g (cylProj _ _) f hab))).2 ?_
    exact isIso_hoEdge_of_eq _ _ ((MoleculeShape.subsingleton_of_dimension_eq_zero _ hP).elim _ _)
  have hunit (γ : Bool) :
      Z.ogp.boundary ⊤ 0 γ = OGP.map we.emb ((unitShape P).ogp.boundary ⊤ 0 γ) :=
    (hglob (!α) γ).symm.trans
      ((congrArg (Z.ogp.boundary · 0 γ) he.symm).trans (we.boundary_image 0 γ))
  have hs' : s ∈ OGP.map we.emb ((unitShape P).ogp.boundary ⊤ 0 false) := by
    rw [← hunit, hZs]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  have ht' : t ∈ OGP.map we.emb ((unitShape P).ogp.boundary ⊤ 0 true) := by
    rw [← hunit, hZt]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  obtain ⟨s', -, hs'⟩ := mem_map.1 hs'
  obtain ⟨t', -, ht'⟩ := mem_map.1 ht'
  let k := we.emb top'
  have hsk' : we.emb s' ≤ k := (isMorphism we.emb).monotone (htop' s')
  have htk' : we.emb t' ≤ k := (isMorphism we.emb).monotone (htop' t')
  have hsk : s ≤ k := hs' ▸ hsk'
  have htk : t ≤ k := ht' ▸ htk'
  have hlw : l ≤ Z.top := Z.le_top l
  have hrw : r ≤ Z.top := Z.le_top r
  have hkw : k ≤ Z.top := Z.le_top k
  have isk : IsIso (hoEdge G hsk) :=
    (prop_hoEdge_iff (fun f => IsIso f) G G hsk hsk'
      (congrArg (G.app _) (edgeOfLE_congr hsk hsk' hs'.symm rfl))).2 (hdeg (htop' s'))
  have itk : IsIso (hoEdge G htk) :=
    (prop_hoEdge_iff (fun f => IsIso f) G G htk htk'
      (congrArg (G.app _) (edgeOfLE_congr htk htk' ht'.symm rfl))).2 (hdeg (htop' t'))
  have hvert : ∀ {W : Shape.Atom} {v : W.ogp} {α : Bool} {S : LowerSet W.ogp},
      W.ogp.boundary S 0 α = .Iic v → W.ogp.boundary (.Iic v) 0 true = .Iic v := by
    intro W v α S h
    have hv : v ∈ W.ogp.boundary S 0 α := h ▸ LowerSet.mem_Iic_iff.2 le_rfl
    exact boundary_Iic_of_isMin
      (grade_eq_zero_iff.1 (Nat.le_zero.1 (grade_le_of_mem_boundary hv))) 0 true
  have houtx : outputRel Wx.ogp tx Wx.top := (hvert htx).trans (by rw [Wx.Iic_top, htx])
  have houty : outputRel Wy.ogp ty Wy.top := (hvert hty).trans (by rw [Wy.Iic_top, hty])
  have hout_ml : outputRel Z.ogp m l := by
    have h := boundary_closure_apply_eq (isMap_of_isInclusion wx.emb) houtx
    change outputRel Z.ogp (wy.emb sy) (wx.emb Wx.top)
    rw [← hglue]
    exact h
  have hout_tr : outputRel Z.ogp t r :=
    boundary_closure_apply_eq (isMap_of_isInclusion wy.emb) houty
  have hout_tw : outputRel Z.ogp t Z.top :=
    (hvert hZt).trans (by rw [Z.Iic_top, hZt])
  have hout_rw : outputRel Z.ogp r Z.top := hout_tr.symm.trans hout_tw
  have iml : IsIso (hoEdge G hml) := hM Z z m l hml hout_ml
  have irw : IsIso (hoEdge G hrw) := hM Z z r Z.top hrw hout_rw
  have itw : IsIso (hoEdge G (htk.trans hkw)) := hM Z z t Z.top _ hout_tw
  obtain ⟨hmono, hepi, hiff⟩ := triangle_hoEdge G hsl hml hmr hsk htk hlw hrw hkw
  have hex := invertorPairRealize_within U hU n g wx (Wx.le_top sx)
  have hey := invertorPairRealize_within U hU n g wy (Wy.le_top sy)
  exact ⟨(prop_hoEdge_iff (fun f => IsSplitMono f) _ _ _ _ hex).1 hmono,
    (prop_hoEdge_iff (fun f => IsSplitEpi f) _ _ _ _ hey).1 hepi,
    (prop_hoEdge_iff (fun f => IsIso f) _ _ _ _ hex).symm.trans
      (hiff.trans (prop_hoEdge_iff (fun f => IsIso f) _ _ _ _ hey))⟩

private theorem eq_top_or_mem_boundary_zero {W : Shape.Atom} (h1 : W.dimension = 1)
    (a : W.ogp) : a = W.top ∨ a ∈ W.ogp.boundary ⊤ 0 false ∨
      a ∈ W.ogp.boundary ⊤ 0 true := by
  by_cases ha : a = W.top
  · exact Or.inl ha
  have hfull : a ∈ W.ogp.bdryFull ⊤ := (W.mem_bdryFull_top_iff a).2 ha
  have hpos : 0 < W.dimension := by omega
  rw [bdryFull, LowerSet.mem_sup_iff, W.bdry_top_eq_boundary hpos,
    W.bdry_top_eq_boundary hpos, h1] at hfull
  exact Or.inr hfull

private theorem isIso_hoEdge_le_top [F.Quasicategory] {W : Shape.Atom} (h1 : W.dimension = 1)
    (G : nerve (ULift.{u} W.ogp) ⟶ F) {sW : W.ogp}
    (hsW : W.ogp.boundary ⊤ 0 false = .Iic sW) (hiso : IsIso (hoEdge G (W.le_top sW)))
    (hout : ∀ (a b : W.ogp) (hab : a ≤ b), outputRel W.ogp a b → IsIso (hoEdge G hab))
    (a : W.ogp) : IsIso (hoEdge G (W.le_top a)) := by
  have hvert : ∀ {v : W.ogp} {α : Bool}, W.ogp.boundary ⊤ 0 α = .Iic v →
      ∀ a ∈ W.ogp.boundary ⊤ 0 α, a = v := by
    intro v α h a ha
    have hv : v ∈ W.ogp.boundary ⊤ 0 α := h ▸ LowerSet.mem_Iic_iff.2 le_rfl
    rw [h] at ha
    exact (isMin_grade_iff.1 (isMin_iff_eq_bot.2 (Nat.le_zero.1
      (grade_le_of_mem_boundary hv)))).eq_of_le (LowerSet.mem_Iic_iff.1 ha)
  obtain ⟨tW, -, htW⟩ := exists_boundary_zero_eq_Iic W.isMolecule true
  rcases eq_top_or_mem_boundary_zero h1 a with rfl | ha | ha
  · exact isIso_hoEdge_of_eq G _ rfl
  · obtain rfl := hvert hsW a ha
    exact hiso
  · have hd : IsMin a := grade_eq_zero_iff.1 (Nat.le_zero.1 (grade_le_of_mem_boundary ha))
    obtain rfl := hvert htW a ha
    exact hout _ _ _ ((boundary_Iic_of_isMin hd 0 true).trans (by rw [W.Iic_top, htW]))

private theorem weakEquivalence_markedFaceNerve_map_markedAboveMap_invertorPair_of_dimension_eq_one
    (U : Shape.Atom) (hU : 0 < U.dimension) (h1 : U.dimension = 1) :
    WeakEquivalence (markedFaceNerve.{u}.map (MarkedDiagSet.markedAboveMap (invertorPair U hU)
      (Nat.sub_le U.dimension 1))) := by
  let n := U.dimension - 1
  let j := MarkedDiagSet.markedAboveMap (invertorPair U hU) (Nat.sub_le U.dimension 1)
  have : CategoryTheory.IsIso (MarkedPresheaf.forget.map j) :=
    inferInstanceAs (CategoryTheory.IsIso (𝟙 _))
  have := isIso_forget_map_markedFaceNerve_map j
  refine weakEquivalence_of_isIso_forget_map _ fun F _ g hg e he => ?_
  have hM : ∀ (W : Shape.Atom) (c : (invertorPair U hU).obj (op W)) (a b : W.ogp)
      (hab : a ≤ b), outputRel W.ogp a b →
        IsIso (hoEdge (invertorPairRealize U hU n g (ofCell c).map) hab) := by
    intro W c a b hab hout
    refine (isIso_hoEdge_iff _ hab).2 ?_
    have hmk : (MarkedPresheaf.forget.map (markedFaceNerveCell
        (X := MarkedDiagSet.markedAbove (invertorPair U hU) U.dimension)
        (x := (MarkedSite.unmarked atomMarking).obj W) c)).app _ (edgeOfLE hab) ∈
        (markedFaceNerve.obj (MarkedDiagSet.markedAbove (invertorPair U hU)
          U.dimension)).marked ⦋1⦌ :=
      MarkedPresheaf.map_mem_marked _
        ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 ⟨rfl, Or.inl hout⟩)
    have hc := markedFaceNerveCell_comp j (x := (MarkedSite.unmarked atomMarking).obj W) c
    have e₁ : (invertorPairRealize U hU n g (ofCell c).map).app _ (edgeOfLE hab) =
        (MarkedPresheaf.forget.map (markedFaceNerve.map j) ≫ g).app _
          ((MarkedPresheaf.forget.map (markedFaceNerveCell
            (X := MarkedDiagSet.markedAbove (invertorPair U hU) U.dimension)
            (x := (MarkedSite.unmarked atomMarking).obj W) c)).app _ (edgeOfLE hab)) :=
      (congrArg (fun k => (k ≫ g).app _ (edgeOfLE hab))
        (realizeFaceNerve_ofCell (Y := MarkedDiagSet.markedAbove (invertorPair U hU) n) c)).trans
        (congrArg (fun (k : markedFaceNerveSite.obj ((MarkedSite.unmarked atomMarking).obj W) ⟶
          markedFaceNerve.obj (MarkedDiagSet.markedAbove (invertorPair U hU) n)) =>
            (MarkedPresheaf.forget.map k ≫ g).app _ (edgeOfLE hab)) hc)
    exact (congrArg (fun x => Nonempty (Edge.mk' x).InvStruct) e₁).mpr (hg _ hmk)
  let A := topInversionData U hU
  let uY : (invertorPair U hU).obj (op U) := (toInvertorPair U hU).app (op U) ⟨𝟙 U⟩
  have hdI (α : Bool) : (A.inverseExtension.shape (⟨⟩, α)).dimension = 1 :=
    (A.dimension_inverseExtension_shape (⟨⟩, α)).trans h1
  obtain ⟨sU, -, hsU⟩ := exists_boundary_zero_eq_Iic U.isMolecule false
  obtain ⟨sL, -, hsL⟩ := exists_boundary_zero_eq_Iic
    (A.inverseExtension.shape (⟨⟩, false)).isMolecule false
  obtain ⟨sR, -, hsR⟩ := exists_boundary_zero_eq_Iic
    (A.inverseExtension.shape (⟨⟩, true)).isMolecule false
  have hP (α : Bool) : ((A.shape ⟨⟩).toMoleculeShape.boundary ((A.shape ⟨⟩).dimension - 1)
      α).dimension = 0 :=
    (MoleculeShape.dimension_boundary _ (Nat.sub_le _ _) α).trans (Nat.sub_eq_zero_of_le h1.le)
  obtain ⟨wu, wl, wε, hε, hp⟩ := A.exists_withins_next_cell ⟨⟩ false
  obtain ⟨hmono, -, hL⟩ := isSplitMono_and_isSplitEpi_of_withins U hU n g hM wu wl wε
    (hP false) h1 hp hε hsU hsL
  obtain ⟨wu, wr, wε, hε, hp⟩ := A.exists_withins_next_cell ⟨⟩ true
  obtain ⟨-, hepi, hR⟩ := isSplitMono_and_isSplitEpi_of_withins U hU n g hM wr wu wε
    (hP true) h1 hp hε hsR hsU
  have hu : IsIso (hoEdge (invertorPairRealize U hU n g (ofCell uY).map) (U.le_top sU)) :=
    @isIso_of_mono_of_isSplitEpi _ _ _ _ _ (@IsSplitMono.mono _ _ _ _ _ hmono) hepi
  have hall_u := isIso_hoEdge_le_top h1 _ hsU hu (hM U uY)
  have hall (α : Bool) : ∀ a, IsIso (hoEdge (invertorPairRealize U hU n g
      (ofCell (A.invertorExtension.incl.app _ (A.inverseExtension.cell (⟨⟩, α)))).map)
      ((A.inverseExtension.shape (⟨⟩, α)).le_top a)) := by
    cases α
    · exact isIso_hoEdge_le_top (hdI false) _ hsL (hL.1 hu) (hM _ _)
    · exact isIso_hoEdge_le_top (hdI true) _ hsR (hR.2 hu) (hM _ _)
  have htrans : ∀ {W V : Shape.Atom} (c₀ : (invertorPair U hU).obj (op W)) (f : V ⟶ W)
      [CategoryTheory.IsIso f] (e' : (nerve (ULift.{u} V.ogp)) _⦋1⦌)
      (he' : (e'.obj 1).down = V.top),
      (∀ a, IsIso (hoEdge (invertorPairRealize U hU n g (ofCell c₀).map) (W.le_top a))) →
      Nonempty (Edge.mk' ((invertorPairRealize U hU n g
        (ofCell ((invertorPair U hU).map f.op c₀)).map).app _ e')).InvStruct := by
    intro W V c₀ f _ e' he' hW
    have e₀ : e' = edgeOfLE (obj_zero_le_obj_one e') :=
      nerve.ext_of_isThin (n := op ⦋1⦌) (funext fun i => by fin_cases i <;> rfl)
    have e₁ := congrArg (fun (Φ : realize.obj (Shape.atomToRDCpx.obj V) ⟶ invertorPair U hU) =>
      (invertorPairRealize U hU n g Φ).app (op ⦋1⦌) e') (ofCell_map_op_map f c₀)
    have e₂ := invertorPairRealize_comp U hU n g (Shape.atomToRDCpx.map f) (ofCell c₀).map
      (obj_zero_le_obj_one e')
    have e₀' := congrArg (fun x => (invertorPairRealize U hU n g
      (realize.map (Shape.atomToRDCpx.map f) ≫ (ofCell c₀).map)).app (op ⦋1⦌) x) e₀
    have e₃ : (edgeOfLE ((ConcreteCategory.hom (Shape.atomToRDCpx.map f).hom).isMap.monotone
        (obj_zero_le_obj_one e')) : (nerve (ULift.{u} W.ogp)) _⦋1⦌) =
          edgeOfLE (W.le_top (f (e'.obj 0).down)) :=
      edgeOfLE_congr _ _ rfl ((congrArg (f ·) he').trans (iso_hom_apply_top (asIso f)))
    refine (congrArg (fun x => Nonempty (Edge.mk' x).InvStruct) (e₁.trans (e₀'.trans (e₂.trans
      (congrArg _ e₃))))).mpr ?_
    exact (isIso_hoEdge_iff _ _).1 (hW _)
  rcases mem_marked_markedFaceNerve he with ⟨x, s, e', he', rfl⟩ | ⟨v, rfl⟩
  · let c : (invertorPair U hU).obj (op x.obj) :=
      (MarkedDiagSet.markedAbove (invertorPair U hU) n).obj.map (MarkedSite.toSelf x).op s
    have ec : g.app _ ((MarkedPresheaf.forget.map (markedFaceNerveCell s)).app _ e') =
        (invertorPairRealize U hU n g (ofCell c).map).app (op ⦋1⦌) e' := by
      have h₁ := congrArg (fun k => (k ≫ g).app (op ⦋1⦌) e')
        (forget_map_markedFaceNerveCell_toSelf s).symm
      have h₂ := congrArg (fun k => (k ≫ g).app (op ⦋1⦌) e')
        (realizeFaceNerve_ofCell (Y := MarkedDiagSet.markedAbove (invertorPair U hU) n) c).symm
      exact h₁.trans h₂
    refine (congrArg (fun x => Nonempty (Edge.mk' x).InvStruct) ec).mpr ?_
    have e₀ : e' = edgeOfLE (obj_zero_le_obj_one e') :=
      nerve.ext_of_isThin (n := op ⦋1⦌) (funext fun i => by fin_cases i <;> rfl)
    obtain ⟨-, h | ⟨⟨-, hmax⟩, hd⟩⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 he'
    · refine (congrArg (fun x => Nonempty (Edge.mk' ((invertorPairRealize U hU n g
        (ofCell c).map).app (op ⦋1⦌) x)).InvStruct) e₀).mpr ?_
      exact (isIso_hoEdge_iff _ _).1 (hM _ c _ _ _ h)
    have htop : (e'.obj 1).down = x.obj.top := eq_top_of_isMax hmax
    have hV1 : x.obj.dimension = 1 := x.obj.dimension_eq.trans ((congrArg _ htop).symm.trans hd)
    rcases isDegenerate_or_isIso_invertorPair U hU (by omega : U.dimension ≤
        x.obj.dimension) c with
      ⟨W, p, y, hp₁, hp₂, hpy⟩ | ⟨f, hf, hfc⟩ | ⟨⟨⟨⟩, α⟩, f, hf, hfc⟩ | ⟨j', f, hf, hfc⟩
    · have e₁ := congrArg (fun (Φ : realize.obj (Shape.atomToRDCpx.obj x.obj) ⟶
        invertorPair U hU) => (invertorPairRealize U hU n g Φ).app (op ⦋1⦌) e')
        ((congrArg (fun c' => (ofCell c').map) hpy.symm).trans (ofCell_map_op_map p y))
      have e₀' := congrArg (fun x => (invertorPairRealize U hU n g
        (realize.map (Shape.atomToRDCpx.map p) ≫ (ofCell y).map)).app (op ⦋1⦌) x) e₀
      have e₂ := invertorPairRealize_comp U hU n g (Shape.atomToRDCpx.map p) (ofCell y).map
        (obj_zero_le_obj_one e')
      refine (congrArg (fun x => Nonempty (Edge.mk' x).InvStruct) (e₁.trans (e₀'.trans e₂))).mpr ?_
      exact (isIso_hoEdge_iff _ _).1 (isIso_hoEdge_of_eq _ _
        (apply_eq_of_degeneracy ⟨hp₁, hp₂⟩ hV1 _ _))
    · have : CategoryTheory.IsIso f := hf
      have hfc' : c = (invertorPair U hU).map f.op uY :=
        hfc.symm.trans ((congrArg ((toInvertorPair U hU).app (op x.obj))
          (congrArg ULift.up (Category.comp_id f).symm)).trans
            (NatTrans.naturality_apply (toInvertorPair U hU) f.op ⟨𝟙 U⟩))
      rw [hfc']
      exact htrans uY f e' htop hall_u
    · have : CategoryTheory.IsIso f := hf
      rw [← hfc]
      exact htrans _ f e' htop (hall α)
    · exfalso
      have h₁ : x.obj.dimension = (A.next.shape j').dimension :=
        Shape.Atom.dimension_eq_of_iso (@asIso _ _ _ _ f hf)
      have h₂ : (A.next.shape j').dimension = U.dimension + 1 :=
        A.dimension_next_shape j'
      omega
  · have hn := SSet.σ_naturality_apply g 0 v
    refine (congrArg (fun x => Nonempty (Edge.mk' x).InvStruct) hn).mpr ?_
    exact ⟨(Edge.InvStruct.invStructId _).ofEq rfl⟩

end InvertorPairArrow

section Generators

theorem weakEquivalence_markedFaceNerve_map_markedAboveMap_invertorPair (U : Shape.Atom)
    (hU : 0 < U.dimension) :
    WeakEquivalence (markedFaceNerve.{u}.map (MarkedDiagSet.markedAboveMap (invertorPair U hU)
      (Nat.sub_le U.dimension 1))) := by
  by_cases h1 : U.dimension = 1
  · exact weakEquivalence_markedFaceNerve_map_markedAboveMap_invertorPair_of_dimension_eq_one U hU
      h1
  · have := isIso_markedFaceNerve_map_markedAboveMap_invertorPair U hU (by omega)
    infer_instance

theorem weakEquivalence_markedFaceNerve_map_of_generators ⦃A B : MarkedDiagSet.{u}⦄ (j : A ⟶ B)
    (hj : (compositorHorns ⊔ invertorHorns ⊔ markingGeneratorsAbove 1 ⊔ invertorGenerators) j) :
    WeakEquivalence (markedFaceNerve.{u}.map j) := by
  rcases hj with ((hj | hj) | hj) | hj
  · cases hj with
    | mk U => exact weakEquivalence_markedFaceNerve_map_compositorMarkedHorn U.1 U.2
  · cases hj with
    | mk p => exact weakEquivalence_markedFaceNerve_map_invertorMarkedHorn p.1.1 p.2 p.1.2
  · cases hj with
    | mk U =>
      have hU : 1 < U.1.dimension := by exact_mod_cast U.2
      have := isIso_markedFaceNerve_map_markingInclusion U.1 hU
      infer_instance
  · cases hj with
    | mk U => exact weakEquivalence_markedFaceNerve_map_markedAboveMap_invertorPair U.1 U.2

end Generators

end Atoms.Diagrammatic
