import Atoms.Molecule.Construction.GlobeComap
import Atoms.Molecule.FlowGraphTree
import Atoms.Molecule.Gluing.Generated
import Atoms.Molecule.MoleculeShape.AtomBoundaryIso
import Atoms.Molecule.MoleculeShape.ParallelAtom
import Atoms.Molecule.MoleculeShape.PositiveOpetope

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

def IsManyToOne (P : OGP.{u}) : Prop :=
  ∀ x : P, 0 < grade ℕ x → ∃! y : P, y ∈ P.faces true x

instance decidableIsManyToOne {P : OGP.{u}} [Fintype P] [DecidableLE P] :
    Decidable (IsManyToOne P) :=
  decidable_of_iff (∀ x : P, 0 < grade ℕ x → (Finset.univ.filter (· ∈ P.faces true x)).card = 1)
    (forall_congr' fun _ => imp_congr_right fun _ => (Fintype.existsUnique_iff_card_one _).symm)

section Faces

variable {P Q : OGP.{u}}

private theorem existsUnique_mem_image_iff (f : P ⟶ Q) [IsInclusion f] (S : Set P) :
    (∃! y, y ∈ f '' S) ↔ ∃! x, x ∈ S := by
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, hu⟩
    exact ⟨x, hx, fun x' hx' => IsInclusion.injective (f := f) (hu _ ⟨x', hx', rfl⟩)⟩
  · rintro ⟨x, hx, hu⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    rw [hu x' hx']

private theorem existsUnique_faces_apply_iff (f : P ⟶ Q) [IsInclusion f] (x : P) (α : Bool) :
    (∃! y, y ∈ Q.faces α (f x)) ↔ ∃! y, y ∈ P.faces α x := by
  rw [← ((isMorphism f).bijOn_faces x α).image_eq]
  exact existsUnique_mem_image_iff f _

private theorem existsUnique_facesIn_map_iff (f : P ⟶ Q) [IsInclusion f] (U : LowerSet P)
    (k : ℕ) (α : Bool) :
    (∃! y, y ∈ Q.facesIn ↑(map f U) k α) ↔ ∃! y, y ∈ P.facesIn ↑U k α := by
  rw [coe_map, ← image_facesIn]
  exact existsUnique_mem_image_iff f _

private theorem mem_facesIn_iff {U : LowerSet P} {n : ℕ} {α : Bool} {y : P} :
    y ∈ P.facesIn ↑U n α ↔ y ∈ P.boundary U n α ∧ grade ℕ y = n :=
  ⟨fun h => ⟨mem_boundary_of_mem_facesIn h le_rfl, h.2.1⟩,
    fun h => mem_facesIn_of_mem_boundary h.1 h.2⟩

private theorem IsGlobular.facesIn_boundary {U : LowerSet P} (hU : P.IsGlobular U) {k n : ℕ}
    (hk : k ≤ n) {α β : Bool} (h : k < n ∨ α = β) :
    P.facesIn ↑(P.boundary U n β) k α = P.facesIn ↑U k α :=
  facesIn_eq_of_boundary_eq (hU.boundary_boundary_eq_of_le hk h)

end Faces

section LemmaFour

private abbrev UniqueOutputs (P : OGP.{u}) : Prop :=
  ∀ k : ℕ, (k : WithBot ℕ∞) < krullDim (⊤ : LowerSet P) → ∃! y : P, y ∈ P.facesIn Set.univ k true

private theorem isManyToOne_and_uniqueOutputs_point :
    IsManyToOne point.{u} ∧ UniqueOutputs point.{u} := by
  have h0 (x : point.{u}) : grade ℕ x = 0 := grade_eq_zero_iff.2 (isMin_point x)
  refine ⟨fun x hx => absurd (h0 x) hx.ne', fun k hk => ?_⟩
  have hle : krullDim (⊤ : LowerSet point.{u}) ≤ (0 : ℕ) := by
    rw [LowerSet.krullDim_top]
    exact krullDim_le_coe_iff.2 fun x => (h0 x).le
  exact absurd (hk.trans_le hle) (by exact_mod_cast Nat.not_lt_zero k)

private theorem isManyToOne_and_uniqueOutputs_of_iso {P Q : OGP.{u}} (e : P ≅ Q)
    (h : IsManyToOne P ∧ UniqueOutputs P) : IsManyToOne Q ∧ UniqueOutputs Q := by
  refine ⟨fun x hx => ?_, fun k hk => ?_⟩
  · have h' := (existsUnique_faces_apply_iff e.hom (e.inv x) true).2
      (h.1 _ (by rwa [(isMorphism e.inv).grade_eq]))
    rwa [Iso.inv_hom_id_apply] at h'
  · have hd : krullDim (⊤ : LowerSet Q) = krullDim (⊤ : LowerSet P) := by
      rw [LowerSet.krullDim_top, LowerSet.krullDim_top]
      exact (krullDim_eq_of_orderIso (orderIsoOfIso e)).symm
    have h' := (existsUnique_facesIn_map_iff e.hom ⊤ k true).2
      (by rw [LowerSet.coe_top]; exact h.2 k (hd ▸ hk))
    rwa [map_top_of_isIso, LowerSet.coe_top] at h'

private theorem isManyToOne_and_uniqueOutputs_pastingAt {U V : OGP.{u}} {n : ℕ} {x : V}
    (hx : x ∈ V.boundary ⊤ n false)
    (φ : U.restrict (U.boundary ⊤ n true) ≅ V.restrict (LowerSet.Iic x))
    (hUm : IsMolecule U) (hVm : IsMolecule V) (hr : (pastingAt (α := false) φ).IsRound ⊤)
    (hVr : V.IsRound ⊤) (hUd : krullDim U = n + 1) (hVd : krullDim V = n + 1)
    (hU : IsManyToOne U ∧ UniqueOutputs U) (hV : IsManyToOne V ∧ UniqueOutputs V) :
    IsManyToOne (pastingAt (α := false) φ) ∧ UniqueOutputs (pastingAt (α := false) φ) := by
  refine ⟨fun z hz => ?_, fun k hk => ?_⟩
  · rcases glue.exists_inl_or_inr z with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · exact (existsUnique_faces_apply_iff (glue.inl φ) p true).2
        (hU.1 p (by rwa [← (isMorphism (glue.inl φ)).grade_eq]))
    · exact (existsUnique_faces_apply_iff (glue.inr φ) q true).2
        (hV.1 q (by rwa [← (isMorphism (glue.inr φ)).grade_eq]))
  · have hW : V.IsSubmoleculeOf (LowerSet.Iic x) (V.boundary ⊤ n false) :=
      (hVm.boundary n false).Iic_isSubmoleculeOf hx
    have hb : (pastingAt (α := false) φ).boundary ⊤ n true =
        map (glue.inr φ) (V.boundary ⊤ n true) := by
      rw [map_boundary]
      exact (isPastingAtIn_pastingAt (k := n) (α := false) φ hW hUm hVm).boundary_not
    have hd : krullDim (⊤ : LowerSet (pastingAt (α := false) φ)) = n + 1 := by
      rw [← glue.map_inl_sup_map_inr φ, LowerSet.krullDim_sup, krullDim_map, krullDim_map,
        LowerSet.krullDim_top, LowerSet.krullDim_top, hUd, hVd, sup_idem]
    have hkn : k ≤ n := by
      rw [hd] at hk
      exact Nat.lt_succ_iff.1 (by exact_mod_cast hk)
    rw [← LowerSet.coe_top, ← hr.isGlobular.facesIn_boundary hkn (Or.inr rfl), hb,
      existsUnique_facesIn_map_iff, hVr.isGlobular.facesIn_boundary hkn (Or.inr rfl),
      LowerSet.coe_top]
    exact hV.2 k (by rw [LowerSet.krullDim_top, hVd]; exact_mod_cast Nat.lt_succ_of_le hkn)

private theorem isManyToOne_and_uniqueOutputs_globe_one :
    IsManyToOne (globe.{u} 1) ∧ UniqueOutputs (globe.{u} 1) := by
  have h3 : UniqueOutputs (globe.{u} 1) := fun k hk => by
    have hk0 : k = 0 := by
      rw [LowerSet.krullDim_top, krullDim_globe] at hk
      exact Nat.lt_one_iff.1 (by exact_mod_cast hk)
    subst hk0
    have hb := boundary_globe.{u} 1 0 Nat.one_pos true
    rw [← LowerSet.coe_top]
    refine ⟨globeFace 1 0 Nat.one_pos true, mem_facesIn_iff.2 ⟨by
      rw [hb]; exact LowerSet.mem_Iic_iff.2 le_rfl, grade_globeFace 1 0 _ true⟩,
      fun y hy => ?_⟩
    have hy' : y ∈ (globe.{u} 1).boundary ⊤ 0 true ∧ grade ℕ y = 0 := mem_facesIn_iff.1 hy
    rw [hb] at hy'
    exact GradeOrder.eq_of_le_of_grade_le (LowerSet.mem_Iic_iff.1 hy'.1)
      (by rw [grade_globeFace, hy'.2])
  refine ⟨fun x hx => ?_, h3⟩
  obtain rfl : x = ⊤ := GradeOrder.eq_of_le_of_grade_le le_top (by rw [grade_top_globe]; omega)
  rw [← Set.ext (fun z => mem_facesIn_Iic_iff_mem_faces (n := 0) (grade_top_globe 1)
    (z := z) true), ← LowerSet.coe_Iic, LowerSet.Iic_top, LowerSet.coe_top]
  exact h3 0 (by rw [LowerSet.krullDim_top, krullDim_globe]; exact_mod_cast Nat.one_pos)

private theorem IsAtom.bdry_bdry_true_le {P : OGP.{u}} (hP : P.IsAtom) {n : ℕ}
    (hd : krullDim (⊤ : LowerSet P) = ↑(n + 1) + 1) (α : Bool) :
    P.bdry (P.bdry ⊤ true) α ≤ P.bdry ⊤ false := by
  have hdb (β : Bool) : krullDim (P.bdry ⊤ β) = (n + 1 : ℕ) :=
    hP.isMoleculeIn.krullDim_bdry (by rw [hd]; push_cast; rfl) β
  rw [← hP.isRound.isGlobular.bdry_bdry_eq hd hdb α]
  exact iSup₂_le fun _ _ => boundary_le _ _ _

private theorem isManyToOne_and_uniqueOutputs_of_bdry {P U : OGP.{u}} {n : ℕ} (hP : P.IsAtom)
    (hd : krullDim (⊤ : LowerSet P) = ↑(n + 1) + 1) (i : U ⟶ P) [IsInclusion i]
    (hi : map i ⊤ = P.bdry ⊤ false) {s : P} (hs : P.bdry ⊤ true = LowerSet.Iic s)
    (hU : IsManyToOne U ∧ UniqueOutputs U) : IsManyToOne P ∧ UniqueOutputs P := by
  obtain ⟨t, ht⟩ := hP.exists_eq_Iic
  have hr := hP.isRound
  have hb (α : Bool) := bdry_eq_boundary hd α
  have hgs : grade ℕ s = n + 1 := by
    have h := hP.isMoleculeIn.krullDim_bdry (by rw [hd]; push_cast; rfl) true
    rw [hs, LowerSet.krullDim_Iic] at h
    exact_mod_cast h
  have hgt : grade ℕ t = n + 1 + 1 := by
    have h := LowerSet.krullDim_Iic t
    rw [← ht, hd] at h
    exact_mod_cast h.symm
  have h3 : UniqueOutputs P := fun k hk => by
    have hk' : k < n + 1 + 1 := by rw [hd] at hk; exact_mod_cast hk
    rw [← LowerSet.coe_top]
    rcases (Nat.lt_succ_iff.1 hk').lt_or_eq with hkn | rfl
    · rw [← hr.isGlobular.facesIn_boundary (n := n + 1) hkn.le (β := false) (Or.inl hkn), ← hb,
        ← hi, existsUnique_facesIn_map_iff, LowerSet.coe_top]
      refine hU.2 k ?_
      rw [← krullDim_map i, hi, hP.isMoleculeIn.krullDim_bdry (by rw [hd]; push_cast; rfl)]
      exact_mod_cast hkn
    · refine ⟨s, mem_facesIn_iff.2 ⟨by rw [← hb, hs]; exact LowerSet.mem_Iic_iff.2 le_rfl, hgs⟩,
        fun y hy => ?_⟩
      have hy' : y ∈ P.boundary ⊤ (n + 1) true ∧ grade ℕ y = n + 1 := mem_facesIn_iff.1 hy
      rw [← hb, hs] at hy'
      exact GradeOrder.eq_of_le_of_grade_le hy'.1 (by rw [hgs, hy'.2])
  refine ⟨fun x hx => ?_, h3⟩
  by_cases hxt : x = t
  · subst hxt
    rw [← Set.ext (fun z => mem_facesIn_Iic_iff_mem_faces hgt (z := z) true),
      ← LowerSet.coe_Iic, ← ht, LowerSet.coe_top]
    exact h3 (n + 1) (by rw [hd]; exact_mod_cast Nat.lt_succ_self (n + 1))
  have key : x = s ∨ x ∈ P.bdry ⊤ false := by
    have hx' : x ∈ P.bdryFull ⊤ := (mem_bdryFull_iff_ne fun y =>
      (ht ▸ LowerSet.mem_top : y ∈ LowerSet.Iic t)).2 hxt
    rcases LowerSet.mem_sup_iff.1 hx' with h | h
    · exact Or.inr h
    rw [hs] at h
    rcases (LowerSet.mem_Iic_iff.1 h).eq_or_lt with h | h
    · exact Or.inl h
    have hx2 : x ∈ (P.bdry (LowerSet.Iic s) false ⊔ P.bdry (LowerSet.Iic s) true : LowerSet P) := by
      rw [← SetLike.mem_coe, coe_bdry_Iic_sup]
      exact h
    rw [← hs] at hx2
    exact Or.inr (sup_le (hP.bdry_bdry_true_le hd false) (hP.bdry_bdry_true_le hd true) hx2)
  rcases key with rfl | hxf
  · rw [← Set.ext (fun z => mem_facesIn_Iic_iff_mem_faces hgs (z := z) true),
      ← LowerSet.coe_Iic, ← hs, hb,
      hr.isGlobular.facesIn_boundary (Nat.le_succ n) (Or.inl (Nat.lt_succ_self n)),
      LowerSet.coe_top]
    exact h3 n (by rw [hd]; exact_mod_cast (by omega : n < n + 1 + 1))
  · rw [← hi] at hxf
    obtain ⟨u, -, rfl⟩ := hxf
    exact (existsUnique_faces_apply_iff i u true).2 (hU.1 u (by rwa [← (isMorphism i).grade_eq]))

private theorem IsPositiveOpetopeTree.isManyToOne_and_uniqueOutputs {P : OGP.{0}}
    (h : IsPositiveOpetopeTree P) : IsManyToOne P ∧ UniqueOutputs P := by
  induction h with
  | point => exact isManyToOne_and_uniqueOutputs_point
  | iso e _ ih => exact isManyToOne_and_uniqueOutputs_of_iso e ih
  | @graft U V n x hx φ hU hV hUd hVd ihU ihV =>
    exact isManyToOne_and_uniqueOutputs_pastingAt hx φ hU.isMolecule hV.isMolecule
      (IsPositiveOpetopeTree.graft hx φ hU hV hUd hVd).isRound hV.isRound hUd hVd ihU ihV
  | shiftPoint => exact isManyToOne_and_uniqueOutputs_globe_one
  | @shift U n hd _ ih =>
    obtain ⟨m, hm⟩ := (U.isAtom_merger hd).exists_eq_Iic
    refine isManyToOne_and_uniqueOutputs_of_bdry (U.isAtom_toMerger hd)
      ((U.toMerger hd).krullDim_top_eq (by rw [U.dimension_toMerger hd, hd])) (U.inputIncl hd)
      (U.map_inputIncl hd) (s := U.outputIncl hd m) ?_ ih
    rw [← U.map_outputIncl hd, hm, map_Iic]

theorem IsPositiveOpetopeTree.existsUnique_faces_true {P : OGP.{0}}
    (h : IsPositiveOpetopeTree P) (x : P) (hx : 0 < grade ℕ x) :
    ∃! y : P, y ∈ P.faces true x :=
  h.isManyToOne_and_uniqueOutputs.1 x hx

theorem IsPositiveOpetopeTree.existsUnique_facesIn_true {P : OGP.{0}}
    (h : IsPositiveOpetopeTree P) {k : ℕ} (hk : (k : WithBot ℕ∞) < krullDim (⊤ : LowerSet P)) :
    ∃! y : P, y ∈ P.facesIn Set.univ k true :=
  h.isManyToOne_and_uniqueOutputs.2 k hk

end LemmaFour

section LemmaFive

private theorem exists_grade_eq_and_grade_le {P : OGP.{u}} {n : ℕ} (h : krullDim P = n + 1) :
    (∃ x : P, grade ℕ x = n + 1) ∧ ∀ x : P, grade ℕ x ≤ n + 1 := by
  have hle : ∀ x : P, grade ℕ x ≤ n + 1 :=
    krullDim_le_coe_iff.1 (by rw [h]; push_cast; rfl)
  obtain ⟨x, hx⟩ := coe_lt_krullDim_iff.1 (by rw [h]; exact_mod_cast Nat.lt_succ_self n)
  exact ⟨⟨x, le_antisymm (hle x) hx⟩, hle⟩

theorem not_exists_isTop_pastingAt {U V : OGP.{u}} {n : ℕ} {α : Bool} {W : LowerSet V}
    (φ : U.restrict (U.boundary ⊤ n (!α)) ≅ V.restrict W) (hUd : krullDim U = n + 1)
    (hVd : krullDim V = n + 1) : ¬ ∃ t : pastingAt φ, IsTop t := by
  rintro ⟨t, ht⟩
  obtain ⟨⟨u, hu⟩, hUle⟩ := exists_grade_eq_and_grade_le hUd
  obtain ⟨⟨v, hv⟩, hVle⟩ := exists_grade_eq_and_grade_le hVd
  have hgt : grade ℕ t ≤ n + 1 := by
    rcases glue.exists_inl_or_inr t with ⟨p, rfl⟩ | ⟨q, rfl⟩
    · rw [(isMorphism (glue.inl φ)).grade_eq]
      exact hUle p
    · rw [(isMorphism (glue.inr φ)).grade_eq]
      exact hVle q
  have hut : glue.inl φ u = t := GradeOrder.eq_of_le_of_grade_le (ht _)
    (by rw [(isMorphism (glue.inl φ)).grade_eq, hu]; exact hgt)
  have hvt : glue.inr φ v = t := GradeOrder.eq_of_le_of_grade_le (ht _)
    (by rw [(isMorphism (glue.inr φ)).grade_eq, hv]; exact hgt)
  obtain ⟨hmem, -⟩ := glue.inl_eq_inr_iff.1 (hut.trans hvt.symm)
  have := grade_le_of_mem_boundary hmem
  omega

private theorem exists_isTop_of_iso {P Q : OGP.{u}} (e : P ≅ Q) (h : ∃ t : Q, IsTop t) :
    ∃ t : P, IsTop t := by
  obtain ⟨t, ht⟩ := h
  refine ⟨e.inv t, fun x => ?_⟩
  rw [← Iso.hom_inv_id_apply e x]
  exact (isMorphism e.inv).monotone (ht _)

private theorem IsPositiveOpetopeTree.nonempty_iso_of_exists_isTop {P : OGP.{0}}
    (h : IsPositiveOpetopeTree P) (ht : ∃ t : P, IsTop t) :
    Nonempty (P ≅ OGP.point) ∨ Nonempty (P ≅ globe 1) ∨
      ∃ (U : RoundShape) (n : ℕ) (hd : U.dimension = n + 1),
        IsPositiveOpetopeTree U.ogp ∧ Nonempty (P ≅ (U.toMerger hd).ogp) := by
  induction h with
  | point => exact Or.inl ⟨Iso.refl _⟩
  | iso e _ ih =>
    rcases ih (exists_isTop_of_iso e ht) with f | f | ⟨U, n, hd, hU, f⟩
    · exact Or.inl (f.map (e.symm ≪≫ ·))
    · exact Or.inr (Or.inl (f.map (e.symm ≪≫ ·)))
    · exact Or.inr (Or.inr ⟨U, n, hd, hU, f.map (e.symm ≪≫ ·)⟩)
  | @graft U V n x hx φ _ _ hUd hVd =>
    exact absurd ht (not_exists_isTop_pastingAt (α := false) φ hUd hVd)
  | shiftPoint => exact Or.inr (Or.inl ⟨Iso.refl _⟩)
  | shift U hd hU => exact Or.inr (Or.inr ⟨U, _, hd, hU, ⟨Iso.refl _⟩⟩)

theorem isPositiveOpetope_iff {P : OGP.{0}} (h : IsPositiveOpetopeTree P) :
    IsPositiveOpetope P ↔
      Nonempty (P ≅ point) ∨ Nonempty (P ≅ globe 1) ∨
        ∃ (U : RoundShape) (n : ℕ) (hd : U.dimension = n + 1),
          IsPositiveOpetopeTree U.ogp ∧ Nonempty (P ≅ (U.toMerger hd).ogp) := by
  refine ⟨fun hP => h.nonempty_iso_of_exists_isTop hP.2, fun h' => ⟨h, ?_⟩⟩
  rcases h' with f | f | ⟨U, n, hd, hU, f⟩
  · exact f.elim fun f => exists_isTop_of_iso f ⟨⊤, isTop_top⟩
  · exact f.elim fun f => exists_isTop_of_iso f ⟨⊤, isTop_top⟩
  · exact f.elim fun f => exists_isTop_of_iso f (isPositiveOpetope_toMerger U hd hU).2

end LemmaFive

section PropositionNine

variable {P : OGP.{u}}

theorem IsManyToOne.exists_facesIn_eq (hP : P.IsMolecule) (hr : P.IsRound ⊤)
    (hm : IsManyToOne P) {n : ℕ} (hn : krullDim (⊤ : LowerSet P) = n + 1) :
    ∃ r : P, grade ℕ r = n + 1 ∧ P.facesIn Set.univ n true = P.faces true r := by
  simpa only [LowerSet.mem_top, true_and, LowerSet.coe_top] using hP.exists_facesIn_eq hr
    (by simpa using hn) (fun x _ hx => hm x (by omega))

private theorem nonempty_iso_restrict_bdry {X Y : OGP.{u}} (f : X ⟶ Y) [IsInclusion f]
    {S : LowerSet Y} (hS : map f ⊤ = S) (α : Bool) :
    Nonempty (X.restrict (X.bdry ⊤ α) ≅ Y.restrict (Y.bdry S α)) := by
  obtain ⟨e, -⟩ := exists_iso_restrict_map f (X.bdry ⊤ α)
  rw [map_bdry, hS] at e
  exact ⟨e⟩

private theorem nonempty_iso_point_restrict {X : OGP.{u}} {S : LowerSet X} (hS : IsMoleculeIn X S)
    (hd : krullDim S = 0) : Nonempty (point.{u} ≅ X.restrict S) := by
  obtain ⟨v, hv, rfl⟩ := hS.exists_eq_Iic_of_krullDim_eq_zero hd
  exact ⟨isoPointRestrictIic hv⟩

private theorem nonempty_iso_of_bdry_iso {X Y : OGP.{0}} (hX : X.IsAtom) (hY : Y.IsAtom) {n : ℕ}
    (hXd : krullDim (⊤ : LowerSet X) = n + 1) (hYd : krullDim (⊤ : LowerSet Y) = n + 1)
    (φ : ∀ α, Nonempty (X.restrict (X.bdry ⊤ α) ≅ Y.restrict (Y.bdry ⊤ α))) :
    Nonempty (X ≅ Y) := by
  obtain ⟨V, hV, ⟨eX⟩⟩ := (isGeneratedMolecule_iff_exists_finiteOGP X).1
    ((isGeneratedMolecule_iff_isMolecule X).2 hX.isMoleculeIn)
  obtain ⟨W, hW, ⟨eY⟩⟩ := (isGeneratedMolecule_iff_exists_finiteOGP Y).1
    ((isGeneratedMolecule_iff_isMolecule Y).2 hY.isMoleculeIn)
  have hdim {Z : OGP.{0}} (S : MoleculeShape) (e : Z ≅ S.ogp)
      (hZ : krullDim (⊤ : LowerSet Z) = n + 1) : S.dimension = n + 1 := by
    have h := S.krullDim_eq_dimension
    rw [← krullDim_eq_of_orderIso (orderIsoOfIso e), ← LowerSet.krullDim_top, hZ] at h
    exact_mod_cast h.symm
  have hdV := hdim ⟨V, hV⟩ eX hXd
  have hdW := hdim ⟨W, hW⟩ eY hYd
  have ψ (α : Bool) :
      Nonempty (V.ogp.restrict (V.ogp.bdry ⊤ α) ≅ W.ogp.restrict (W.ogp.bdry ⊤ α)) :=
    ⟨(nonempty_iso_restrict_bdry eX.inv (map_top_of_isIso _) α).some ≪≫ (φ α).some ≪≫
      (nonempty_iso_restrict_bdry eY.hom (map_top_of_isIso _) α).some⟩
  obtain ⟨e⟩ := MoleculeShape.nonempty_iso_of_boundary_iso ⟨V, hV⟩ ⟨W, hW⟩
    (fun α => MoleculeShape.bdryIso _ hdV α ≪≫ (ψ α).some ≪≫ (MoleculeShape.bdryIso _ hdW α).symm)
    ((isAtom_iff_of_iso eX).1 hX) ((isAtom_iff_of_iso eY).1 hY) hdV hdW
  exact ⟨eX ≪≫ e ≪≫ eY.symm⟩

private theorem IsManyToOne.restrict (hm : IsManyToOne P) (S : LowerSet P) :
    IsManyToOne (P.restrict S) := fun x hx =>
  (existsUnique_faces_apply_iff (incl S) x true).1
    (hm _ (by rwa [(isMorphism (incl S)).grade_eq]))

private theorem isPositiveOpetopeTree_of_isAtom {n : ℕ}
    (ih : ∀ X : OGP.{0}, X.IsMolecule → X.IsRound ⊤ → IsManyToOne X →
      krullDim (⊤ : LowerSet X) = n → IsPositiveOpetopeTree X)
    {P : OGP.{0}} (hP : P.IsAtom) (hm : IsManyToOne P) (hd : krullDim (⊤ : LowerSet P) = n + 1) :
    IsPositiveOpetopeTree P := by
  obtain ⟨t, ht⟩ := hP.exists_eq_Iic
  have hgt : grade ℕ t = n + 1 := by
    have h := LowerSet.krullDim_Iic t
    rw [← ht, hd] at h
    exact_mod_cast h.symm
  obtain ⟨r, hr, hru⟩ := hm t (by omega)
  have hQ₁ : (P.restrict (P.bdry ⊤ true)).IsAtom := by
    rw [ht, bdry_Iic, Set.eq_singleton_iff_unique_mem.2 ⟨hr, hru⟩, lowerClosure_singleton]
    exact (hP.isMoleculeIn.isAtomIn_Iic LowerSet.mem_top).isAtom_restrict
  cases n with
  | zero =>
    have hpt {X : OGP.{0}} (hX : X.IsAtom) (hXd : krullDim (⊤ : LowerSet X) = (0 : ℕ) + 1)
        (α : Bool) : Nonempty (point.{0} ≅ X.restrict (X.bdry ⊤ α)) :=
      nonempty_iso_point_restrict (by rw [bdry_eq_boundary hXd]; exact hX.isMoleculeIn.boundary 0 α)
        (hX.isMoleculeIn.krullDim_bdry (by rw [hXd]; rfl) α)
    have hGd : krullDim (⊤ : LowerSet (globe.{0} 1)) = (0 : ℕ) + 1 := by
      rw [LowerSet.krullDim_top, krullDim_globe]
      rfl
    obtain ⟨e⟩ := nonempty_iso_of_bdry_iso (isAtom_globe 1) hP hGd hd fun α =>
      ⟨(hpt (isAtom_globe 1) hGd α).some.symm ≪≫ (hpt hP hd α).some⟩
    exact .iso e .shiftPoint
  | succ n =>
    have hQ₀ : (P.restrict (P.bdry ⊤ false)).IsMolecule := (isMolecule_restrict_iff _).2
      (by rw [bdry_eq_boundary hd]; exact hP.isMoleculeIn.boundary _ false)
    obtain ⟨V, hV, ⟨e₀⟩⟩ := (isGeneratedMolecule_iff_exists_finiteOGP _).1
      ((isGeneratedMolecule_iff_isMolecule _).2 hQ₀)
    have hQ₀d : krullDim (⊤ : LowerSet (P.restrict (P.bdry ⊤ false))) = (n + 1 : ℕ) := by
      rw [LowerSet.krullDim_top, hP.krullDim_restrict_bdry hd false]
    let U : RoundShape :=
      ⟨⟨V, hV⟩, (isRound_top_iff_of_iso e₀).2 (hP.isRound_restrict_bdry hd false)⟩
    have hUd : U.dimension = n + 1 := by
      have h := U.krullDim_eq_dimension
      rw [← krullDim_eq_of_orderIso (orderIsoOfIso e₀), ← LowerSet.krullDim_top, hQ₀d] at h
      exact_mod_cast h.symm
    have hU : IsPositiveOpetopeTree U.ogp :=
      .iso e₀ (ih _ hQ₀ (hP.isRound_restrict_bdry hd false) (hm.restrict _) hQ₀d)
    have hb (β : Bool) := hP.isRound.isGlobular.bdry_bdry_eq hd
      (fun γ => hP.isMoleculeIn.krullDim_bdry (by rw [hd]; push_cast; rfl) γ) β
    have hmerger : Nonempty (P.restrict (P.bdry ⊤ true) ≅ (U.merger hUd).ogp) := by
      refine nonempty_iso_of_bdry_iso hQ₁ (U.isAtom_merger hUd)
        (by rw [LowerSet.krullDim_top, hP.krullDim_restrict_bdry hd true]; push_cast; rfl)
        ((U.merger hUd).krullDim_top_eq (by rw [U.dimension_merger hUd, hUd])) fun β => ?_
      obtain ⟨e₁⟩ := nonempty_iso_restrict_bdry (incl (P.bdry ⊤ true)) (map_incl_top _) β
      obtain ⟨e₂⟩ := nonempty_iso_restrict_bdry (incl (P.bdry ⊤ false)) (map_incl_top _) β
      obtain ⟨e₃⟩ := nonempty_iso_restrict_bdry e₀.hom (map_top_of_isIso _) β
      obtain ⟨e₄, -⟩ := exists_iso_restrict (U.mergerIncl hUd β) (U.map_mergerIncl hUd β)
      rw [← hb] at e₁
      exact ⟨e₁ ≪≫ e₂.symm ≪≫ e₃ ≪≫ (U.bdryIso hUd β).symm ≪≫ e₄⟩
    obtain ⟨e⟩ := nonempty_iso_of_bdry_iso hP (U.isAtom_toMerger hUd) hd
      ((U.toMerger hUd).krullDim_top_eq (by rw [U.dimension_toMerger hUd, hUd])) fun α => by
        cases α
        · obtain ⟨e₁, -⟩ := exists_iso_restrict (U.inputIncl hUd) (U.map_inputIncl hUd)
          exact ⟨e₀ ≪≫ e₁⟩
        · obtain ⟨e₁, -⟩ := exists_iso_restrict (U.outputIncl hUd) (U.map_outputIncl hUd)
          exact hmerger.map (· ≪≫ e₁)
    exact .iso e.symm (.shift U hUd hU)

private theorem isPositiveOpetopeTree_restrict_of_isPastingAtIn {P : OGP.{0}} {n : ℕ}
    {S T R : LowerSet P} (hp : P.IsPastingAtIn n false S T R) {y : P}
    (hy : P.boundary S n true = LowerSet.Iic y) (hS : IsPositiveOpetopeTree (P.restrict S))
    (hT : IsPositiveOpetopeTree (P.restrict T)) (hSd : krullDim S = n + 1)
    (hTd : krullDim T = n + 1) : IsPositiveOpetopeTree (P.restrict R) := by
  have hinf : S ⊓ T = LowerSet.Iic y := hp.inf_eq.trans hy
  have hyST : y ∈ S ⊓ T := hinf ▸ LowerSet.mem_Iic_iff.2 le_rfl
  let y' : P.restrict T := ⟨y, hyST.2⟩
  have hBS : map (incl S) ((P.restrict S).boundary ⊤ n true) = LowerSet.Iic y := by
    rw [map_boundary, map_incl_top, hy]
  obtain ⟨eS, heS⟩ := exists_iso_restrict (incl ((P.restrict S).boundary ⊤ n true) ≫ incl S)
    (by rw [map_comp, map_incl_top, hBS])
  obtain ⟨eT, heT⟩ := exists_iso_restrict (C := LowerSet.Iic y) (incl (LowerSet.Iic y') ≫ incl T)
    (by rw [map_comp, map_incl_top, map_Iic, incl_apply])
  let φ := eS ≪≫ eT.symm
  have hφ (a : (P.restrict S).restrict ((P.restrict S).boundary ⊤ n true)) :
      (((φ.hom a : (P.restrict T).restrict (LowerSet.Iic y')) : P.restrict T) : P) =
        ((a : P.restrict S) : P) := by
    have h1 := ConcreteCategory.congr_hom heT (φ.hom a)
    have h2 := ConcreteCategory.congr_hom heS a
    simp only [ConcreteCategory.comp_apply, incl_apply] at h1 h2
    rw [← h1, ← h2]
    exact congrArg Subtype.val (eT.inv_hom_id_apply (eS.hom a))
  have hx : y' ∈ (P.restrict T).boundary ⊤ n false := by
    have h : incl T y' ∈ map (incl T) ((P.restrict T).boundary ⊤ n false) := by
      rw [map_boundary, map_incl_top]
      exact hp.isSubmoleculeOf_inf.le hyST
    rwa [apply_mem_map_iff] at h
  obtain ⟨Θ, -⟩ := exists_iso_of_cover_pair (glue.inl φ) (glue.inr φ)
    (codRestrict (incl S) R fun a => hp.left_le a.2)
    (codRestrict (incl T) R fun b => hp.right_le b.2) (glue.map_inl_sup_map_inr φ)
    (top_unique fun r _ => by
      have hr : (r : P) ∈ S ⊔ T := hp.eq_sup ▸ r.2
      rcases LowerSet.mem_sup_iff.1 hr with h | h
      exacts [Or.inl ⟨⟨r, h⟩, trivial, rfl⟩, Or.inr ⟨⟨r, h⟩, trivial, rfl⟩]) fun a b => by
    rw [glue.inl_eq_inr_iff]
    refine ⟨fun ⟨h, hab⟩ => restrict_ext ?_, fun hab => ?_⟩
    · simp only [codRestrict_apply, incl_apply]
      exact (hφ ⟨a, h⟩).symm.trans (congrArg Subtype.val hab)
    · have hv : (a : P) = (b : P) := by simpa using congrArg Subtype.val hab
      have ha : incl S a ∈ map (incl S) ((P.restrict S).boundary ⊤ n true) := by
        rw [hBS, ← hinf, incl_apply]
        exact LowerSet.mem_inf_iff.2 ⟨a.2, by rw [hv]; exact b.2⟩
      rw [apply_mem_map_iff] at ha
      exact ⟨ha, restrict_ext ((hφ _).trans hv)⟩
  exact .iso Θ (.graft hx φ hS hT hSd hTd)

private theorem isPositiveOpetopeTree_restrict_layerSuffix_and_krullDim {n : ℕ} {P : OGP.{0}}
    (hd : krullDim (⊤ : LowerSet P) = n + 1) {L : List (LowerSet P)} (hL : IsLayering P n ⊤ L)
    {o : P} (ho : grade ℕ o = n) (hbo : P.boundary ⊤ n true = LowerSet.Iic o)
    (hcl : ∀ t : P, grade ℕ t = n + 1 → IsPositiveOpetopeTree (P.restrict (LowerSet.Iic t)))
    (hbt : ∀ t : P, grade ℕ t = n + 1 →
      ∃ w ∈ P.faces true t, P.boundary (LowerSet.Iic t) n true = LowerSet.Iic w)
    {j : ℕ} (hj : j < L.length) :
    IsPositiveOpetopeTree (P.restrict (layerSuffix ⊤ n L j)) ∧
      krullDim (layerSuffix ⊤ n L j) = n + 1 := by
  have hd' : krullDim (⊤ : LowerSet P) = (n + 1 : ℕ) := by rw [hd]; push_cast; rfl
  have hdIic (t : P) (ht : grade ℕ t = n + 1) : krullDim (LowerSet.Iic t) = n + 1 := by
    rw [LowerSet.krullDim_Iic, ht]
    push_cast
    rfl
  obtain ⟨d, hjd⟩ : ∃ d, j + d + 1 = L.length := ⟨L.length - j - 1, by omega⟩
  induction d generalizing j with
  | zero =>
    obtain ⟨t, htL, hdt, hdL, hu⟩ := hL.exists_top_getD hd' hj
    have hpj := hL.isPastingIn_layerSuffix hj
    rw [show j + 1 = L.length by omega, layerSuffix_length, hbo] at hpj
    have hbm := (hL.isPastingIn_layerPrefix_layerSuffix (j := L.length) le_rfl).2
    rw [layerSuffix_length, hbo] at hbm
    have hp : P.IsPastingAtIn n false (.Iic t) (.Iic o) (layerSuffix ⊤ n L j) :=
      isPastingAtIn_Iic_of_isPastingIn (hL.isMoleculeIn_getD hj) htL hdt hdL hu false hpj hbm
    obtain ⟨w, hwf, hw⟩ := hbt t hdt
    have hwm : w ∈ LowerSet.Iic t ⊓ LowerSet.Iic o := by
      rw [hp.inf_eq, Bool.not_false, hw]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    have hwo : w = o := GradeOrder.eq_of_le_of_grade_le (LowerSet.mem_Iic_iff.1 hwm.2) (by
      have := Nat.covBy_iff_add_one_eq.1 (hwf.1.grade ℕ)
      rw [ho]
      omega)
    have hsj : layerSuffix ⊤ n L j = LowerSet.Iic t := by
      rw [hp.eq_sup, sup_eq_left]
      exact LowerSet.Iic_le.2 (hwo ▸ hwm.1)
    rw [hsj]
    exact ⟨hcl t hdt, hdIic t hdt⟩
  | succ d ih =>
    obtain ⟨t, htL, hdt, hdL, hu⟩ := hL.exists_top_getD hd' hj
    obtain ⟨hY, hYd⟩ := ih (j := j + 1) (by omega) (by omega)
    have hp : P.IsPastingAtIn n false (.Iic t) (layerSuffix ⊤ n L (j + 1))
        (layerSuffix ⊤ n L j) :=
      isPastingAtIn_Iic_of_isPastingIn (hL.isMoleculeIn_getD hj) htL hdt hdL hu false
        (hL.isPastingIn_layerSuffix hj)
        (hL.isPastingIn_layerPrefix_layerSuffix (j := j + 1) (by omega)).2
    obtain ⟨w, -, hw⟩ := hbt t hdt
    exact ⟨isPositiveOpetopeTree_restrict_of_isPastingAtIn hp hw (hcl t hdt) hY (hdIic t hdt) hYd,
      le_antisymm (hd ▸ LowerSet.krullDim_mono le_top)
        (hdIic t hdt ▸ LowerSet.krullDim_mono hp.left_le)⟩

private theorem isPositiveOpetopeTree_of_isAtom_succ {n : ℕ}
    (hatom : ∀ X : OGP.{0}, X.IsAtom → IsManyToOne X → krullDim (⊤ : LowerSet X) = n + 1 →
      IsPositiveOpetopeTree X)
    {P : OGP.{0}} (hP : P.IsMolecule) (hr : P.IsRound ⊤) (hm : IsManyToOne P)
    (hd : krullDim (⊤ : LowerSet P) = n + 1) : IsPositiveOpetopeTree P := by
  have hd' : krullDim (⊤ : LowerSet P) = (n + 1 : ℕ) := by rw [hd]; push_cast; rfl
  obtain ⟨L, hL⟩ := admitsLayering_pred_krullDim hP hd' (Nat.succ_pos n)
  rw [Nat.add_sub_cancel] at hL
  have hcl (t : P) (ht : grade ℕ t = n + 1) : IsPositiveOpetopeTree (P.restrict (LowerSet.Iic t)) :=
    hatom _ (hP.isAtomIn_Iic LowerSet.mem_top).isAtom_restrict (hm.restrict _) (by
      rw [LowerSet.krullDim_top]
      exact (LowerSet.krullDim_Iic t).trans (by rw [ht]; push_cast; rfl))
  have hbt (t : P) (ht : grade ℕ t = n + 1) :
      ∃ w ∈ P.faces true t, P.boundary (LowerSet.Iic t) n true = LowerSet.Iic w := by
    obtain ⟨w, hw, hwu⟩ := hm t (by omega)
    exact ⟨w, hw, by rw [boundary_Iic ht, Set.eq_singleton_iff_unique_mem.2 ⟨hw, hwu⟩,
      lowerClosure_singleton]⟩
  obtain ⟨_, _, _, o, _, hUo, _⟩ :=
    hP.exists_root_graph hr hd' (fun x _ hx => hm x (by omega))
  have ho : o ∈ P.facesIn (⊤ : LowerSet P) n true := by
    rw [hUo]
    exact Set.mem_singleton o
  have hou : ∀ y, y ∈ P.facesIn (⊤ : LowerSet P) n true → y = o := by
    intro y hy
    rwa [hUo, Set.mem_singleton_iff] at hy
  have hbo : P.boundary ⊤ n true = LowerSet.Iic o := by
    refine le_antisymm (fun e he => ?_) (LowerSet.Iic_le.2 (mem_boundary_of_mem_facesIn ho le_rfl))
    obtain ⟨z, hez, hz⟩ := (hP.boundary n true).exists_le_maximal he
    have hzn := (hr.boundary n true).grade_eq_of_maximal
      (hP.krullDim_boundary (by rw [hd']; exact_mod_cast Nat.le_succ n) true) hz
    exact hez.trans (hou z (mem_facesIn_of_mem_boundary hz.prop hzn)).le
  obtain ⟨h, -⟩ := isPositiveOpetopeTree_restrict_layerSuffix_and_krullDim hd hL ho.2.1 hbo hcl
    hbt (List.length_pos_iff.2 hL.ne_nil)
  rw [hL.layerSuffix_zero] at h
  obtain ⟨e, -⟩ := exists_iso_restrict (𝟙 P) (map_top_of_isIso _)
  exact .iso e.symm h

private theorem isPositiveOpetopeTree_of_isManyToOne (n : ℕ) {P : OGP.{0}} (hP : P.IsMolecule)
    (hr : P.IsRound ⊤) (hm : IsManyToOne P) (hd : krullDim (⊤ : LowerSet P) = n) :
    IsPositiveOpetopeTree P := by
  induction n generalizing P with
  | zero =>
    obtain ⟨e⟩ := nonempty_iso_point_restrict (S := ⊤) hP (by rw [hd, Nat.cast_zero])
    obtain ⟨e', -⟩ := exists_iso_restrict (𝟙 P) (map_top_of_isIso _)
    exact .iso (e ≪≫ e'.symm) .point
  | succ n ih =>
    exact isPositiveOpetopeTree_of_isAtom_succ (fun X hX hmX hXd =>
      isPositiveOpetopeTree_of_isAtom (fun Y hY hrY hmY hYd => ih hY hrY hmY hYd) hX hmX hXd)
      hP hr hm (hd.trans (Nat.cast_succ n))

theorem isPositiveOpetopeTree_iff {P : OGP.{0}} :
    IsPositiveOpetopeTree P ↔ P.IsMolecule ∧ P.IsRound ⊤ ∧ IsManyToOne P := by
  refine ⟨fun h => ⟨h.isMolecule, h.isRound, fun x hx => h.existsUnique_faces_true x hx⟩,
    fun ⟨hP, hr, hm⟩ => ?_⟩
  obtain ⟨n, hn⟩ := hP.exists_krullDim_eq
  exact isPositiveOpetopeTree_of_isManyToOne n hP hr hm hn

instance decidableIsPositiveOpetopeTree (P : OGP.{0}) [Fintype P] [DecidableEq P]
    [DecidableLE P] : Decidable (IsPositiveOpetopeTree P) :=
  decidable_of_iff _ isPositiveOpetopeTree_iff.symm

theorem IsPositiveOpetopeTree.restrict_boundary {P : OGP.{0}}
    (h : IsPositiveOpetopeTree P) (n : ℕ) (α : Bool) :
    IsPositiveOpetopeTree (P.restrict (P.boundary ⊤ n α)) := by
  obtain ⟨hP, hr, hm⟩ := isPositiveOpetopeTree_iff.1 h
  refine isPositiveOpetopeTree_iff.2 ⟨(isMolecule_restrict_iff _).2 (hP.boundary n α), ?_,
    hm.restrict _⟩
  rw [← isRound_map_iff (incl _), map_incl_top]
  exact hr.boundary n α

theorem IsPositiveOpetopeTree.isPositiveOpetope_restrict_Iic {P : OGP.{0}}
    (h : IsPositiveOpetopeTree P) (x : P) :
    IsPositiveOpetope (P.restrict (LowerSet.Iic x)) := by
  obtain ⟨hP, -, hm⟩ := isPositiveOpetopeTree_iff.1 h
  have ha := (hP.isAtomIn_Iic (LowerSet.mem_top (a := x))).isAtom_restrict
  exact ⟨isPositiveOpetopeTree_iff.2 ⟨ha.isMoleculeIn, ha.isRound, hm.restrict _⟩,
    ⟨x, le_rfl⟩, fun y => y.2⟩

end PropositionNine

end Atoms.Molecule.OGP
