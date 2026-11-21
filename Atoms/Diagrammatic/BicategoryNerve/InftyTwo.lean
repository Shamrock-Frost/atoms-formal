import Atoms.Diagrammatic.BicategoryNerve.Filler
import Atoms.Diagrammatic.Marked.FlatEquivalence

open CategoryTheory Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open Atoms.Diagrammatic.PastingDiagram
open CategoryTheory.Bicategory (PathCell pathComp)
open scoped CategoryTheory.Bicategory

universe w v u

namespace Atoms.Diagrammatic

attribute [local instance high] instFintypeRdc instFintypeRestrict instDecidableMemBdryFullAtom

section EquivalentOfCell

variable {X : DiagSet.{u}}

theorem Equivalent.of_hasRoundType {u v : RoundPastingDiagram X} {U : Atom} {x : diagram X U}
    (hx : HasRoundType (PastingDiagram.ofCell x) u v) (hm : IsEquivalence X x) :
    Equivalent u v :=
  EquivalenceData.equivalent ⟨hx.dim_eq_dim, cellRound x, hm, hx.dim_eq, hx.source, hx.target⟩

end EquivalentOfCell

variable {B : Type u} [Bicategory.{w, v} B]

namespace Parallel

variable {s t : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)} (h : Parallel s t)

noncomputable def labellingOfThreeLe (hs : 3 ≤ s.dim) (b₀ : B) :
    Labelling B h.cellShape.rdc.obj.toOGP h.cellShape.rdc.obj.isRDC :=
  h.sphereLabelling.extend (P := h.cellShape.rdc.obj.toOGP) (hP := h.cellShape.rdc.obj.isRDC) b₀
    (fun e he => absurd (e.2.1.symm.trans (h.grade_of_not_mem_bdryFull he)) (by omega))
    (fun _ hx _ _ _ _ hxM => absurd (hx.symm.trans (h.grade_of_not_mem_bdryFull hxM)) (by omega))

theorem comap_labellingOfThreeLe (hs : 3 ≤ s.dim) (b₀ : B) :
    (h.labellingOfThreeLe hs b₀).comap (P := (h.cellShape.rdc.restrict
        (h.cellShape.ogp.bdryFull ⊤)).obj.toOGP)
      (inclMap (P := h.cellShape.rdc.obj.toOGP) (h.cellShape.ogp.bdryFull ⊤))
      (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)).obj.isRDC = h.sphereLabelling :=
  Labelling.comap_extend _ _ _ _

theorem isCommutative_labellingOfThreeLe (hs : 3 ≤ s.dim) (b₀ : B) :
    (h.labellingOfThreeLe hs b₀).IsCommutative := by
  intro y hy
  have hm : y ∈ h.cellShape.ogp.bdryFull ⊤ := by
    by_contra hm
    have := h.grade_of_not_mem_bdryFull hm
    omega
  have key : h.sphereLabelling.IsCommutativeAt ⟨y, hm⟩ := (bicategoryNerveHomEquiv B
    (h.cellShape.rdc.restrict (h.cellShape.ogp.bdryFull ⊤)) h.sphere).2 ⟨y, hm⟩
    (((isMorphism (incl _)).grade_eq ⟨y, hm⟩).trans hy)
  rw [← h.comap_labellingOfThreeLe hs b₀] at key
  exact @Labelling.IsCommutativeAt.of_comap _ _ _ _ _ _ _ _ _ _ (incl _) _ _ _ key

theorem exists_nerveFiller_of_three_le (hs : 3 ≤ s.dim) :
    ∃ x : diagram (bicategoryNerve.{w, v, u} B) h.cellShape,
      HasRoundType (PastingDiagram.ofCell x) s t := by
  have hM : IsMoleculeIn h.cellShape.rdc.obj.toOGP ⊤ := h.cellShape.toMoleculeShape.isMolecule
  let b₀ := h.sphereLabelling.toPrefunctor.obj ⟨_,
    h.mem_bdryFull_of_boundary_zero (boundary_zero_eq_Iic_vertex _ hM false)⟩
  exact ⟨PastingDiagram.nerveCellOf ⟨h.labellingOfThreeLe hs b₀,
    h.isCommutative_labellingOfThreeLe hs b₀⟩,
    h.hasRoundType_nerveCellOf _ (h.comap_labellingOfThreeLe hs b₀)⟩

end Parallel

theorem bicategoryNerve_mem_equivalences_of_four_le
    (e : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)) (he : 4 ≤ e.dim) :
    e ∈ equivalences (bicategoryNerve.{w, v, u} B) :=
  mem_equivalences_of_forall_parallel (k := 3)
    (fun _ _ h hs => ⟨h.cellShape, h.exists_nerveFiller_of_three_le hs⟩) e he

theorem bicategoryNerve_mem_equivalences_of_three_le
    (e : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)) (he : 3 ≤ e.dim) :
    e ∈ equivalences (bicategoryNerve.{w, v, u} B) := by
  rcases he.lt_or_eq with he | he
  · exact bicategoryNerve_mem_equivalences_of_four_le e he
  have hn : e.dim = 2 + 1 := he.symm
  have hb (α : Bool) : (e.boundary 2 α).dim = 2 := dim_boundary _ (by omega) α
  have hpar := parallel_boundary e.isRound hn true false
  obtain ⟨x, hx⟩ := (hpar.exists_nerveFiller_two_iff (hb true) (hb true).le (hb false).le).2
    (PastingDiagram.nerveComposite_boundary_eq e.toPastingDiagram).symm
  refine (mem_equivalences_iff e).2 (biInvWitness_of_forall_parallel hn (e' := cellRound x) hx
    fun s t hst hs => ?_)
  obtain ⟨z, hz⟩ := hst.exists_nerveFiller_of_three_le hs.ge
  exact ⟨cellRound z, bicategoryNerve_mem_equivalences_of_four_le _
    (show 4 ≤ (PastingDiagram.ofCell z).dim by rw [hz.dim_eq]; omega), hz⟩

theorem bicategoryNerve_mem_equivalences_of_isIso
    (e : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)) (he : e.dim = 2) {a b : B}
    {P Q : Quiver.Path a b} {φ : pathComp (𝟭q B) P ⟶ pathComp (𝟭q B) Q}
    (hφ : e.nerveComposite he.le = ⟨a, b, P, Q, φ⟩) [IsIso φ] :
    e ∈ equivalences (bicategoryNerve.{w, v, u} B) := by
  have hn : e.dim = 1 + 1 := he
  have hb (α : Bool) : (e.boundary 1 α).dim = 1 := dim_boundary _ (by omega) α
  have hb₂ (α : Bool) : (e.boundary 1 α).dim ≤ 2 := (hb α).trans_le one_le_two
  have hc₀ : (e.boundary 1 false).nerveComposite (hb₂ false) = ⟨a, b, P, P, 𝟙 _⟩ := by
    rw [PastingDiagram.nerveComposite_boundary_one _ he.le false (hb₂ false), hφ]
    rfl
  have hc₁ : (e.boundary 1 true).nerveComposite (hb₂ true) = ⟨a, b, Q, Q, 𝟙 _⟩ := by
    rw [PastingDiagram.nerveComposite_boundary_one _ he.le true (hb₂ true), hφ]
    rfl
  let a' : RoundPastingDiagram (bicategoryNerve.{w, v, u} B) :=
    ⟨e.boundary 1 false, isRound_boundary_of_isRound e.isRound 1 false⟩
  let b' : RoundPastingDiagram (bicategoryNerve.{w, v, u} B) :=
    ⟨e.boundary 1 true, isRound_boundary_of_isRound e.isRound 1 true⟩
  obtain ⟨x, hx, hxc⟩ := (parallel_boundary e.isRound hn true false).exists_nerveFiller_one
    (hb true) (hb₂ true) (hb₂ false) hc₁ hc₀ (inv φ)
  have he₁ : HasBdry false 1 e.toPastingDiagram a'.toPastingDiagram b'.toPastingDiagram :=
    ⟨hn, hb false, hb true, .refl _, .refl _⟩
  have he₂ : HasBdry false 1 (PastingDiagram.ofCell x) b'.toPastingDiagram a'.toPastingDiagram :=
    .of_dim_eq (hb true) hx.dim_eq (hb true) (hb false) hx.source hx.target
  have hte : HasRoundType e.toPastingDiagram a' b' :=
    .of_equiv_boundary (hb false) (hb true) hn fun β => by cases β <;> exact .refl _
  have hxd : (PastingDiagram.ofCell x).dim ≤ 2 := he₂.dim_h.le
  refine mem_equivalences_of_equivalent_unit (e' := cellRound x) he₁ he₂ a'.isRound b'.isRound
    ?_ ?_
  · have htp := hte.paste hx (.refl _) (hb false) (he₁.pastable he₂ (.refl _))
    have hpd : (e.paste (PastingDiagram.ofCell x) 1 (he₁.pastable he₂ (.refl _))).dim = 2 :=
      htp.dim_eq.trans (congrArg (· + 1) (hb false))
    have hu := PastingDiagram.nerveComposite_unit_of_dim_eq_one a'.toPastingDiagram (hb false)
      ((dim_unit _).trans_le (by rw [hb false])) hc₀
    have hp := PastingDiagram.nerveComposite_pasteAlong_one e.toPastingDiagram
      (PastingDiagram.ofCell x) (he₁.pastable he₂ (.refl _)).1.iso
      (he₁.pastable he₂ (.refl _)).1.map_comm he.le hxd hpd.le hφ (hxc hxd)
    rw [IsIso.hom_inv_id] at hp
    have hpar := HasRoundType.parallel
      (c := ⟨_, isRound_paste_of_dim e (cellRound x) he₁.dim_h he₂.dim_h
        (he₁.pastable he₂ (.refl _))⟩)
      (d := a'.isRound.unit) htp (hasRoundType_unit a')
    have hiff := hpar.exists_nerveFiller_two_iff hpd hpd.le
      ((dim_unit _).trans_le (by rw [hb false]))
    have heq := hp.trans hu.symm
    obtain ⟨z, hz⟩ := hiff.2 heq
    exact Equivalent.of_hasRoundType hz (bicategoryNerve_mem_equivalences_of_three_le _
      (show 3 ≤ (PastingDiagram.ofCell z).dim by
        rw [hz.dim_eq]; exact (congrArg (· + 1) hpd).symm.le))
  · have htq := hx.paste hte (.refl _) (hb true) (he₂.pastable he₁ (.refl _))
    have hqd : ((PastingDiagram.ofCell x).paste e.toPastingDiagram 1
        (he₂.pastable he₁ (.refl _))).dim = 2 :=
      htq.dim_eq.trans (congrArg (· + 1) (hb true))
    have hu := PastingDiagram.nerveComposite_unit_of_dim_eq_one b'.toPastingDiagram (hb true)
      ((dim_unit _).trans_le (by rw [hb true])) hc₁
    have hq := PastingDiagram.nerveComposite_pasteAlong_one (PastingDiagram.ofCell x)
      e.toPastingDiagram (he₂.pastable he₁ (.refl _)).1.iso
      (he₂.pastable he₁ (.refl _)).1.map_comm hxd he.le hqd.le (hxc hxd) hφ
    rw [IsIso.inv_hom_id] at hq
    have hpar := HasRoundType.parallel (c := b'.isRound.unit)
      (d := ⟨_, isRound_paste_of_dim (cellRound x) e he₂.dim_h he₁.dim_h
        (he₂.pastable he₁ (.refl _))⟩)
      (hasRoundType_unit b') htq
    have hiff := hpar.exists_nerveFiller_two_iff ((dim_unit _).trans (by rw [hb true]))
      ((dim_unit _).trans_le (by rw [hb true])) hqd.le
    have heq := hu.trans hq.symm
    obtain ⟨z, hz⟩ := hiff.2 heq
    exact Equivalent.of_hasRoundType hz (bicategoryNerve_mem_equivalences_of_three_le _
      (show 3 ≤ (PastingDiagram.ofCell z).dim by rw [hz.dim_eq, dim_unit, hb true]))

theorem hasWeakComposites_bicategoryNerve : HasWeakComposites (bicategoryNerve.{w, v, u} B) := by
  refine (hasWeakComposites_iff_positive _).2 fun u hu => ?_
  have hn : u.dim = (u.dim - 1) + 1 := (Nat.sub_add_cancel hu).symm
  have hb (α : Bool) : (u.boundary (u.dim - 1) α).dim = u.dim - 1 :=
    dim_boundary _ (Nat.sub_le _ _) α
  have hpar := parallel_boundary u.isRound hn false true
  have hb₀ (α : Bool) (k : ℕ) (hk : u.dim - 1 = k) :
      u.boundary (u.dim - 1) α = u.boundary k α :=
    u.toPastingDiagram.boundary_congr hk α
  obtain h1 | h2 | h3 : u.dim = 1 ∨ u.dim = 2 ∨ 3 ≤ u.dim := by omega
  · have hd : u.dim ≤ 2 := by omega
    have hbd (α : Bool) : (u.boundary (u.dim - 1) α).dim ≤ 2 := by rw [hb α]; omega
    have hz (α : Bool) : (u.boundary 0 α).dim ≤ 2 :=
      (dim_boundary _ (Nat.zero_le _) α).trans_le (Nat.zero_le 2)
    obtain ⟨p, hp⟩ := PastingDiagram.exists_nerveComposite_eq_of_dim_le_one _ hd h1.le
    obtain ⟨c', hc', hcc'⟩ := hpar.exists_nerveFiller_zero (by rw [hb false]; omega) (hbd false)
      (hbd true)
      ((PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq (hb₀ false 0 (by omega)))
        _ (hz false)).trans (PastingDiagram.nerveComposite_boundary_zero _ hd false (hz false)))
      ((PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq (hb₀ true 0 (by omega)))
        _ (hz true)).trans (PastingDiagram.nerveComposite_boundary_zero _ hd true (hz true)))
      (pathComp (𝟭q B) p)
    refine exists_weakComposite_of_cell u hu hpar hc' fun c hc hpu => ?_
    have hcd' : (PastingDiagram.ofCell c').dim ≤ 2 := by rw [hc'.dim_eq, hb false]; omega
    have hcd : (cellRound c).dim ≤ 2 := (dim_eq_of_equiv hc).trans_le hcd'
    obtain ⟨w, hw, hwc⟩ := hpu.exists_nerveFiller_one h1 hd hcd hp
      ((PastingDiagram.nerveComposite_congr hc hcd hcd').trans (hcc' hcd'))
      (λ_ (pathComp (𝟭q B) p)).inv
    exact Equivalent.of_hasRoundType hw (@bicategoryNerve_mem_equivalences_of_isIso _ _
      (cellRound w) (hw.dim_eq.trans (by rw [h1])) _ _ _ _ _ (hwc _) (Iso.isIso_inv _))
  · have hd : u.dim ≤ 2 := h2.le
    have hbd (α : Bool) : (u.boundary (u.dim - 1) α).dim ≤ 2 := by rw [hb α]; omega
    rcases hu' : u.nerveComposite hd with ⟨a, b, P, Q, φ⟩
    have hbc (α : Bool) : (u.boundary (u.dim - 1) α).nerveComposite (hbd α) =
        ⟨a, b, cond α Q P, cond α Q P, 𝟙 _⟩ := by
      rw [PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq (hb₀ α 1 (by omega)))
        _ ((dim_boundary _ (by omega) α).trans_le one_le_two),
        PastingDiagram.nerveComposite_boundary_one _ hd α, hu']
    obtain ⟨c', hc', hcc'⟩ := hpar.exists_nerveFiller_one (by rw [hb false]; omega) (hbd false)
      (hbd true) (hbc false) (hbc true) φ
    refine exists_weakComposite_of_cell u hu hpar hc' fun c hc hpu => ?_
    have hcd' : (PastingDiagram.ofCell c').dim ≤ 2 := by rw [hc'.dim_eq, hb false]; omega
    have hcd : (cellRound c).dim ≤ 2 := (dim_eq_of_equiv hc).trans_le hcd'
    obtain ⟨w, hw⟩ := (hpu.exists_nerveFiller_two_iff h2 hd hcd).2
      (hu'.trans ((hcc' hcd').symm.trans (PastingDiagram.nerveComposite_congr hc hcd hcd').symm))
    exact Equivalent.of_hasRoundType hw (bicategoryNerve_mem_equivalences_of_three_le _
      (show 3 ≤ (PastingDiagram.ofCell w).dim by rw [hw.dim_eq, h2]))
  · obtain ⟨c', hc'⟩ : ∃ c' : diagram (bicategoryNerve.{w, v, u} B) hpar.cellShape,
        HasRoundType (PastingDiagram.ofCell c') _ _ := by
      rcases h3.lt_or_eq with h4 | h3
      · exact hpar.exists_nerveFiller_of_three_le (by rw [hb false]; omega)
      · have hbd (α : Bool) : (u.boundary (u.dim - 1) α).dim ≤ 2 := by rw [hb α]; omega
        refine (hpar.exists_nerveFiller_two_iff (by rw [hb false]; omega) (hbd false)
          (hbd true)).2 ?_
        exact (PastingDiagram.nerveComposite_congr
          (PastingDiagram.equiv_of_eq (hb₀ false 2 (by omega))) _ _).trans
          ((PastingDiagram.nerveComposite_boundary_eq u.toPastingDiagram).trans
            (PastingDiagram.nerveComposite_congr
              (PastingDiagram.equiv_of_eq (hb₀ true 2 (by omega))) _ _).symm)
    refine exists_weakComposite_of_cell u hu hpar hc' fun c _ hpu => ?_
    obtain ⟨w, hw⟩ := hpu.exists_nerveFiller_of_three_le h3
    exact Equivalent.of_hasRoundType hw (bicategoryNerve_mem_equivalences_of_three_le _
      (show 3 ≤ (PastingDiagram.ofCell w).dim by rw [hw.dim_eq]; omega))

theorem isInftyCategory_bicategoryNerve : IsInftyCategory 2 (bicategoryNerve.{w, v, u} B) :=
  ⟨hasWeakComposites_bicategoryNerve, fun U x hU =>
    bicategoryNerve_mem_equivalences_of_three_le (cellRound x) (by
      have : 2 < U.dimension := by exact_mod_cast hU
      exact this)⟩

theorem isFibrant_bicategoryNerve :
    HomotopicalAlgebra.IsFibrant ((DiagSet.toInfty 2).obj (bicategoryNerve.{w, v, u} B)) :=
  (isFibrant_infty_iff 2 _).2 isInftyCategory_bicategoryNerve

theorem isInftyCategory_one_bicategoryNerve (hB : ∀ {a b : B} {f g : a ⟶ b} (φ : f ⟶ g), IsIso φ) :
    IsInftyCategory 1 (bicategoryNerve.{w, v, u} B) := by
  refine ⟨hasWeakComposites_bicategoryNerve, fun U x hU => ?_⟩
  have hU' : 1 < U.dimension := by exact_mod_cast hU
  rcases (show 2 = U.dimension ∨ 3 ≤ U.dimension by omega) with h2 | h3
  · have hd : (cellRound x).dim = 2 := h2.symm
    rcases hc : (cellRound x).nerveComposite hd.le with ⟨a, b, P, Q, φ⟩
    have := hB φ
    exact bicategoryNerve_mem_equivalences_of_isIso (cellRound x) hd hc
  · exact bicategoryNerve_mem_equivalences_of_three_le (cellRound x) h3

theorem nerveComposite_eq_of_equivalent {u v : RoundPastingDiagram (bicategoryNerve.{w, v, u} B)}
    (h : Equivalent u v) (hu : u.dim = 2) (hud : u.dim ≤ 2) (hvd : v.dim ≤ 2) :
    u.nerveComposite hud = v.nerveComposite hvd := by
  obtain ⟨-, e, -, -, hs, ht⟩ := h.data
  have hs' := (PastingDiagram.equiv_of_eq (e.boundary_congr hu.symm false)).trans hs
  have ht' := (PastingDiagram.equiv_of_eq (e.boundary_congr hu.symm true)).trans ht
  exact (PastingDiagram.nerveComposite_congr hs'.symm hud _).trans
    (e.nerveComposite_boundary_eq.trans (PastingDiagram.nerveComposite_congr ht' _ hvd))

end Atoms.Diagrammatic
