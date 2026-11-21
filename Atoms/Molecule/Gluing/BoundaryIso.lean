import Atoms.Molecule.Gluing.Pasting
import Atoms.Molecule.Gluing.Rewrite

universe u

open CategoryTheory Limits Order

namespace Atoms.Molecule.OGP

variable {P M A B : OGP.{u}}

theorem map_hom_incl_top {S : LowerSet P} (e : A ≅ P.restrict S) : map (e.hom ≫ incl S) ⊤ = S := by
  rw [map_comp, map_top_of_isIso, map_incl_top]

private theorem bdry_le_map_incl_top (α : Bool) : A.bdry ⊤ α ≤ map (incl (A.bdryFull ⊤)) ⊤ := by
  rw [map_incl_top]
  exact bdry_le_bdryFull ⊤ α

theorem _root_.CategoryTheory.Iso.IsSigned.map_comap_bdry
    {φ : A.restrict (A.bdryFull ⊤) ≅ B.restrict (B.bdryFull ⊤)} (hφ : φ.IsSigned) (α : Bool) :
    map (φ.hom ≫ incl _) (comap (incl _) (A.bdry ⊤ α)) = B.bdry ⊤ α := by
  refine SetLike.ext fun y => ⟨?_, fun hy => ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact (hφ α x).1 hx
  · have hyB : y ∈ B.bdryFull ⊤ := bdry_le_bdryFull ⊤ α hy
    refine ⟨φ.inv ⟨y, hyB⟩, (hφ α _).2 ?_, ?_⟩
    · change ((φ.hom (φ.inv ⟨y, hyB⟩)) : B) ∈ B.bdry ⊤ α
      rwa [Iso.inv_hom_id_apply]
    · change ((φ.hom (φ.inv ⟨y, hyB⟩)) : B) = y
      rw [Iso.inv_hom_id_apply]

theorem apply_eq_of_map_comap_bdry_eq (hA : A.IsMolecule)
    {f g : A.restrict (A.bdryFull ⊤) ⟶ P} [IsInclusion f] [IsInclusion g]
    (h : ∀ α, map f (comap (incl _) (A.bdry ⊤ α)) = map g (comap (incl _) (A.bdry ⊤ α)))
    (x : A.restrict (A.bdryFull ⊤)) : f x = g x := by
  obtain ⟨α, hα⟩ : ∃ α, x.1 ∈ A.bdry ⊤ α :=
    (LowerSet.mem_sup_iff.1 x.2).elim (⟨false, ·⟩) (⟨true, ·⟩)
  have hpos : 0 < krullDim (⊤ : LowerSet A) := by
    by_contra hd
    rw [bdry_eq_bot (not_lt.1 hd)] at hα
    exact hα
  have hS : IsMoleculeIn (A.restrict (A.bdryFull ⊤)) (comap (incl _) (A.bdry ⊤ α)) := by
    rw [← isMoleculeIn_map_iff (incl _), map_comap_of_le _ (bdry_le_map_incl_top α)]
    exact hA.bdry hpos α
  exact hS.eqOn_of_map_eq _ _ (h α) hα

theorem _root_.CategoryTheory.Iso.IsSigned.eq_of_isMolecule (hA : A.IsMolecule)
    {φ ψ : A.restrict (A.bdryFull ⊤) ≅ B.restrict (B.bdryFull ⊤)} (hφ : φ.IsSigned)
    (hψ : ψ.IsSigned) : φ = ψ := by
  refine Iso.ext ?_
  ext x
  exact apply_eq_of_map_comap_bdry_eq (f := φ.hom ≫ incl _) (g := ψ.hom ≫ incl _) hA
    (fun α => (hφ.map_comap_bdry α).trans (hψ.map_comap_bdry α).symm) x

theorem apply_eq_of_isSigned_of_map_bdry_eq (hA : A.IsMolecule) (eA : A ⟶ P) (eB : B ⟶ P)
    [IsInclusion eA] [IsInclusion eB] (he : ∀ α, map eA (A.bdry ⊤ α) = map eB (B.bdry ⊤ α))
    {φ : A.restrict (A.bdryFull ⊤) ≅ B.restrict (B.bdryFull ⊤)} (hφ : φ.IsSigned)
    (x : A.restrict (A.bdryFull ⊤)) : eB (φ.hom x).1 = eA x.1 :=
  apply_eq_of_map_comap_bdry_eq (f := φ.hom ≫ incl _ ≫ eB) (g := incl _ ≫ eA) hA
    (fun α => by
      rw [← Category.assoc, map_comp _ eB, hφ.map_comap_bdry, map_comp,
        map_comap_of_le _ (bdry_le_map_incl_top α), he]) x

theorem mem_bdryFull_of_map_eq {e : A ⟶ P} {α : Bool} (he : map e ⊤ = P.bdry ⊤ α) (x : A) :
    e x ∈ P.bdryFull ⊤ :=
  bdry_le_bdryFull ⊤ α (he ▸ ⟨x, LowerSet.mem_top, rfl⟩)

def toBdryFull (e : A ⟶ P) {α : Bool} (he : map e ⊤ = P.bdry ⊤ α) :
    A ⟶ P.restrict (P.bdryFull ⊤) :=
  codRestrict e _ (mem_bdryFull_of_map_eq he)

@[simp] theorem toBdryFull_apply (e : A ⟶ P) {α : Bool} (he : map e ⊤ = P.bdry ⊤ α) (x : A) :
    (toBdryFull e he x : P) = e x :=
  rfl

instance (e : A ⟶ P) [IsInclusion e] {α : Bool} (he : map e ⊤ = P.bdry ⊤ α) :
    IsInclusion (toBdryFull e he) :=
  inferInstanceAs (IsInclusion (codRestrict e _ _))

theorem map_toBdryFull_sup {e₀ : A ⟶ P} {e₁ : B ⟶ P} (h₀ : map e₀ ⊤ = P.bdry ⊤ false)
    (h₁ : map e₁ ⊤ = P.bdry ⊤ true) :
    map (toBdryFull e₀ h₀) ⊤ ⊔ map (toBdryFull e₁ h₁) ⊤ = ⊤ := by
  rw [toBdryFull, toBdryFull, map_codRestrict, map_codRestrict, h₀, h₁, eq_top_iff]
  rintro w -
  exact LowerSet.mem_sup_iff.1 w.2

theorem rewrite.isPushout_bdryFull {U V : OGP.{u}} {n : ℕ}
    {φ : U.restrict (U.bdryFull ⊤) ≅ V.restrict (V.bdryFull ⊤)} (hU : U.IsRound ⊤)
    (hV : V.IsRound ⊤) (hUd : krullDim U = n) (hVd : krullDim V = n) :
    IsPushout (incl (U.bdryFull ⊤)) (φ.hom ≫ incl (V.bdryFull ⊤))
      (toBdryFull (rewrite.inl n φ hU hV hUd hVd)
        (rewrite.bdry_top_false n φ hU hV hUd hVd).symm)
      (toBdryFull (rewrite.inr n φ hU hV hUd hVd)
        (rewrite.bdry_top_true n φ hU hV hUd hVd).symm) := by
  refine isPushout_of_cover _ _ ?_ (map_toBdryFull_sup _ _) ?_
  · ext x
    exact ConcreteCategory.congr_hom (rewrite.condition n φ hU hV hUd hVd) x
  · rw [map_comp, map_incl_top, toBdryFull, toBdryFull, map_codRestrict, map_codRestrict,
      map_codRestrict, ← (gc_map_comap _).u_inf, rewrite.map_inl_inf_map_inr]

private theorem toBdryFull_inv {α : Bool} (e : A ≅ P.restrict (P.bdry ⊤ α))
    (z : P.restrict (P.bdryFull ⊤)) (hz : z.1 ∈ P.bdry ⊤ α) :
    toBdryFull (e.hom ≫ incl _) (map_hom_incl_top e) (e.inv ⟨z.1, hz⟩) = z := by
  refine Subtype.ext ?_
  rw [toBdryFull_apply, ConcreteCategory.comp_apply, incl_apply, Iso.inv_hom_id_apply]

private theorem mem_bdry_of_cover {β : Bool} (eA : A ≅ P.restrict (P.bdry ⊤ β))
    (eB : B ≅ P.restrict (P.bdry ⊤ (!β))) (fA : A ≅ M.restrict (M.bdry ⊤ β))
    (fB : B ≅ M.restrict (M.bdry ⊤ (!β)))
    (hc : ∀ x y, (eA.hom x : P) = eB.hom y ↔ (fA.hom x : M) = fB.hom y) (x : A) {α : Bool}
    (h : (eA.hom x : P) ∈ P.bdry ⊤ α) : (fA.hom x : M) ∈ M.bdry ⊤ α := by
  rcases Bool.eq_or_eq_not α β with rfl | rfl
  · exact (fA.hom x).2
  · obtain ⟨y, hy⟩ : ∃ y, (eB.hom y : P) = eA.hom x :=
      ⟨eB.inv ⟨_, h⟩, congrArg Subtype.val (eB.inv_hom_id_apply _)⟩
    rw [(hc x y).1 hy.symm]
    exact (fB.hom y).2

section Cover

variable (eA : A ≅ P.restrict (P.bdry ⊤ false)) (eB : B ≅ P.restrict (P.bdry ⊤ true))
  (fA : A ≅ M.restrict (M.bdry ⊤ false)) (fB : B ≅ M.restrict (M.bdry ⊤ true))
  [DecidablePred (· ∈ P.bdry ⊤ false)]

private def coverFun (z : P.restrict (P.bdryFull ⊤)) : M.restrict (M.bdryFull ⊤) :=
  if h : z.1 ∈ P.bdry ⊤ false then
    ⟨(fA.hom (eA.inv ⟨z.1, h⟩) : M), bdry_le_bdryFull ⊤ false (fA.hom _).2⟩
  else
    ⟨(fB.hom (eB.inv ⟨z.1, (LowerSet.mem_sup_iff.1 z.2).resolve_left h⟩) : M),
      bdry_le_bdryFull ⊤ true (fB.hom _).2⟩

private theorem coverFun_eA (x : A) :
    coverFun eA eB fA fB (toBdryFull (eA.hom ≫ incl _) (map_hom_incl_top eA) x) =
      toBdryFull (fA.hom ≫ incl _) (map_hom_incl_top fA) x := by
  have h : (toBdryFull (eA.hom ≫ incl _) (map_hom_incl_top eA) x).1 ∈ P.bdry ⊤ false :=
    (eA.hom x).2
  refine Subtype.ext ?_
  rw [coverFun, dif_pos h]
  exact congrArg (fun a => (fA.hom a : M)) (eA.hom_inv_id_apply x)

variable (hc : ∀ x y, (eA.hom x : P) = eB.hom y ↔ (fA.hom x : M) = fB.hom y)
include hc

private theorem coverFun_eB (y : B) :
    coverFun eA eB fA fB (toBdryFull (eB.hom ≫ incl _) (map_hom_incl_top eB) y) =
      toBdryFull (fB.hom ≫ incl _) (map_hom_incl_top fB) y := by
  refine Subtype.ext ?_
  by_cases h : (toBdryFull (eB.hom ≫ incl _) (map_hom_incl_top eB) y).1 ∈ P.bdry ⊤ false
  · rw [coverFun, dif_pos h]
    exact (hc _ y).1 (congrArg Subtype.val (eA.inv_hom_id_apply ⟨_, h⟩))
  · rw [coverFun, dif_neg h]
    exact congrArg (fun b => (fB.hom b : M)) (eB.hom_inv_id_apply y)

private theorem isMorphism_coverFun : IsMorphism (coverFun eA eB fA fB) :=
  .of_forall_exists fun z => by
    rcases LowerSet.mem_sup_iff.1 z.2 with hz | hz
    · refine ⟨A, toBdryFull (eA.hom ≫ incl _) (map_hom_incl_top eA), eA.inv ⟨z.1, hz⟩,
        isMorphism _, ?_, toBdryFull_inv eA z hz⟩
      convert isMorphism (toBdryFull (fA.hom ≫ incl _) (map_hom_incl_top fA)) using 1
      exact funext (coverFun_eA eA eB fA fB)
    · refine ⟨B, toBdryFull (eB.hom ≫ incl _) (map_hom_incl_top eB), eB.inv ⟨z.1, hz⟩,
        isMorphism _, ?_, toBdryFull_inv eB z hz⟩
      convert isMorphism (toBdryFull (fB.hom ≫ incl _) (map_hom_incl_top fB)) using 1
      exact funext (coverFun_eB eA eB fA fB hc)

variable [DecidablePred (· ∈ M.bdry ⊤ false)]

def bdryIsoOfCover : P.restrict (P.bdryFull ⊤) ≅ M.restrict (M.bdryFull ⊤) where
  hom := ConcreteCategory.ofHom ⟨coverFun eA eB fA fB, isMorphism_coverFun eA eB fA fB hc⟩
  inv := ConcreteCategory.ofHom ⟨coverFun fA fB eA eB,
    isMorphism_coverFun fA fB eA eB fun x y => (hc x y).symm⟩
  hom_inv_id := hom_ext_of_map_sup_eq_top
    (map_toBdryFull_sup (map_hom_incl_top eA) (map_hom_incl_top eB))
    (by
      ext x
      exact congrArg Subtype.val
        ((congrArg (coverFun fA fB eA eB) (coverFun_eA eA eB fA fB x)).trans
          (coverFun_eA fA fB eA eB x)))
    (by
      ext y
      exact congrArg Subtype.val
        ((congrArg (coverFun fA fB eA eB) (coverFun_eB eA eB fA fB hc y)).trans
          (coverFun_eB fA fB eA eB (fun x y => (hc x y).symm) y)))
  inv_hom_id := hom_ext_of_map_sup_eq_top
    (map_toBdryFull_sup (map_hom_incl_top fA) (map_hom_incl_top fB))
    (by
      ext x
      exact congrArg Subtype.val
        ((congrArg (coverFun eA eB fA fB) (coverFun_eA fA fB eA eB x)).trans
          (coverFun_eA eA eB fA fB x)))
    (by
      ext y
      exact congrArg Subtype.val
        ((congrArg (coverFun eA eB fA fB)
          (coverFun_eB fA fB eA eB (fun x y => (hc x y).symm) y)).trans
            (coverFun_eB eA eB fA fB hc y)))

@[reassoc (attr := simp)]
theorem toBdryFull_bdryIsoOfCover_hom_left :
    toBdryFull (eA.hom ≫ incl _) (map_hom_incl_top eA) ≫ (bdryIsoOfCover eA eB fA fB hc).hom =
      toBdryFull (fA.hom ≫ incl _) (map_hom_incl_top fA) := by
  ext x
  exact congrArg Subtype.val (coverFun_eA eA eB fA fB x)

@[reassoc (attr := simp)]
theorem toBdryFull_bdryIsoOfCover_hom_right :
    toBdryFull (eB.hom ≫ incl _) (map_hom_incl_top eB) ≫ (bdryIsoOfCover eA eB fA fB hc).hom =
      toBdryFull (fB.hom ≫ incl _) (map_hom_incl_top fB) := by
  ext y
  exact congrArg Subtype.val (coverFun_eB eA eB fA fB hc y)

theorem isSigned_bdryIsoOfCover : (bdryIsoOfCover eA eB fA fB hc).IsSigned := by
  intro α w
  rcases LowerSet.mem_sup_iff.1 w.2 with hw | hw
  · obtain ⟨x, rfl⟩ : w ∈ Set.range (toBdryFull (eA.hom ≫ incl _) (map_hom_incl_top eA)) :=
      ⟨eA.inv ⟨w.1, hw⟩, toBdryFull_inv eA w hw⟩
    have hl := ConcreteCategory.congr_hom (toBdryFull_bdryIsoOfCover_hom_left eA eB fA fB hc) x
    rw [ConcreteCategory.comp_apply] at hl
    rw [hl]
    exact ⟨mem_bdry_of_cover eA eB fA fB hc x,
      mem_bdry_of_cover fA fB eA eB (fun x y => (hc x y).symm) x⟩
  · obtain ⟨y, rfl⟩ : w ∈ Set.range (toBdryFull (eB.hom ≫ incl _) (map_hom_incl_top eB)) :=
      ⟨eB.inv ⟨w.1, hw⟩, toBdryFull_inv eB w hw⟩
    have hr := ConcreteCategory.congr_hom (toBdryFull_bdryIsoOfCover_hom_right eA eB fA fB hc) y
    rw [ConcreteCategory.comp_apply] at hr
    rw [hr]
    exact ⟨mem_bdry_of_cover eB eA fB fA (fun y x => eq_comm.trans ((hc x y).trans eq_comm)) y,
      mem_bdry_of_cover fB fA eB eA (fun y x => eq_comm.trans ((hc x y).symm.trans eq_comm)) y⟩

end Cover

theorem IsMoleculeIn.bdry_bdry_eq {U : LowerSet P} (h : IsMoleculeIn P U) (α : Bool) :
    P.bdry (P.bdry U false) α = P.bdry (P.bdry U true) α := by
  obtain ⟨n, hn⟩ := h.exists_krullDim_eq
  cases n with
  | zero =>
    have h0 : krullDim U ≤ 0 := by rw [hn, Nat.cast_zero]
    rw [bdry_eq_bot (U := U) h0 false, bdry_eq_bot (U := U) h0 true]
  | succ m =>
    have hU : krullDim U = m + 1 := by rw [hn]; push_cast; rfl
    refine h.isGlobular.bdry_bdry_eq hU (fun β => ?_) α
    rw [bdry_eq_boundary hU]
    exact h.krullDim_boundary (by rw [hn]; exact_mod_cast Nat.le_succ m) β

section Merger

variable (hP : P.IsMolecule) {β : Bool} (eA : A ≅ P.restrict (P.bdry ⊤ β))
  (eB : B ≅ P.restrict (P.bdry ⊤ (!β)))

include hP in
theorem map_bdryFull_eq_of_isMolecule :
    map (eA.hom ≫ incl _) (A.bdryFull ⊤) = map (eB.hom ≫ incl _) (B.bdryFull ⊤) := by
  rw [map_bdryFull, map_bdryFull, map_hom_incl_top, map_hom_incl_top]
  cases β <;> simp only [Bool.not_false, Bool.not_true, bdryFull, hP.bdry_bdry_eq]

include hP eB in
private theorem exists_apply_eq (x : A.restrict (A.bdryFull ⊤)) :
    ∃ y ∈ B.bdryFull ⊤, (eB.hom y : P) = eA.hom x.1 := by
  obtain ⟨y, hyB, hy⟩ : (eA.hom x.1 : P) ∈ map (eB.hom ≫ incl _) (B.bdryFull ⊤) :=
    map_bdryFull_eq_of_isMolecule hP eA eB ▸ ⟨x.1, x.2, rfl⟩
  exact ⟨y, hyB, hy⟩

include hP eB in
private theorem mem_bdry_not (x : A.restrict (A.bdryFull ⊤)) :
    (eA.hom x.1 : P) ∈ P.bdry ⊤ (!β) :=
  let ⟨y, _, hy⟩ := exists_apply_eq hP eA eB x
  hy ▸ (eB.hom y).2

include hP in
private theorem inv_mem_bdryFull (x : A.restrict (A.bdryFull ⊤)) :
    (eB.inv ⟨(eA.hom x.1 : P), mem_bdry_not hP eA eB x⟩ : B) ∈ B.bdryFull ⊤ := by
  obtain ⟨y, hyB, hy⟩ := exists_apply_eq hP eA eB x
  have e : (⟨(eA.hom x.1 : P), mem_bdry_not hP eA eB x⟩ : P.restrict (P.bdry ⊤ (!β))) =
      eB.hom y :=
    Subtype.ext hy.symm
  rw [e, Iso.hom_inv_id_apply]
  exact hyB

private def mergerHom : A.restrict (A.bdryFull ⊤) ⟶ B.restrict (B.bdryFull ⊤) :=
  codRestrict (codRestrict (incl _ ≫ eA.hom ≫ incl _) _ (mem_bdry_not hP eA eB) ≫ eB.inv) _
    (inv_mem_bdryFull hP eA eB)

private theorem apply_mergerHom (x : A.restrict (A.bdryFull ⊤)) :
    (eB.hom (mergerHom hP eA eB x).1 : P) = eA.hom x.1 :=
  congrArg Subtype.val (eB.inv_hom_id_apply (⟨_, mem_bdry_not hP eA eB x⟩ : P.restrict _))

end Merger

section Merger

variable (hP : P.IsMolecule) (eA : A ≅ P.restrict (P.bdry ⊤ false))
  (eB : B ≅ P.restrict (P.bdry ⊤ true))

def mergerGluing : A.restrict (A.bdryFull ⊤) ≅ B.restrict (B.bdryFull ⊤) where
  hom := mergerHom hP eA eB
  inv := mergerHom hP eB eA
  hom_inv_id := by
    ext x
    exact IsInclusion.injective (f := eA.hom) (Subtype.ext
      ((apply_mergerHom hP eB eA _).trans (apply_mergerHom hP eA eB x)))
  inv_hom_id := by
    ext y
    exact IsInclusion.injective (f := eB.hom) (Subtype.ext
      ((apply_mergerHom hP eA eB _).trans (apply_mergerHom hP eB eA y)))

theorem apply_mergerGluing (x : A.restrict (A.bdryFull ⊤)) :
    (eB.hom ((mergerGluing hP eA eB).hom x).1 : P) = eA.hom x.1 :=
  apply_mergerHom hP eA eB x

theorem isSigned_mergerGluing : (mergerGluing hP eA eB).IsSigned := by
  intro α x
  change x.1 ∈ A.bdry ⊤ α ↔ ((mergerGluing hP eA eB).hom x).1 ∈ B.bdry ⊤ α
  rw [← apply_mem_map_iff (eA.hom ≫ incl _), ← apply_mem_map_iff (eB.hom ≫ incl _),
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, incl_apply, incl_apply,
    apply_mergerGluing, map_bdry, map_bdry, map_hom_incl_top, map_hom_incl_top,
    hP.bdry_bdry_eq]

theorem apply_eq_apply_iff_mergerGluing (hr : P.IsRound ⊤) (hd : 0 < krullDim (⊤ : LowerSet P))
    (x : A) (y : B) :
    (eA.hom x : P) = eB.hom y ↔
      ∃ h : x ∈ A.bdryFull ⊤, ((mergerGluing hP eA eB).hom ⟨x, h⟩).1 = y := by
  refine ⟨fun hxy => ?_, fun ⟨h, hy⟩ => ?_⟩
  · obtain ⟨n, hn⟩ := hP.exists_krullDim_eq
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (n := n) (by
      rintro rfl
      rw [hn] at hd
      exact lt_irrefl _ hd)
    have hU : krullDim (⊤ : LowerSet P) = m + 1 := by rw [hn]; push_cast; rfl
    have hm : (eA.hom x : P) ∈ P.bdry ⊤ false ⊓ P.bdry ⊤ true := ⟨(eA.hom x).2, hxy ▸ (eB.hom y).2⟩
    rw [hr.bdry_inf_bdry hU (by
      rw [bdry_eq_boundary hU]
      exact hP.krullDim_boundary (by rw [hn]; exact_mod_cast Nat.le_succ m) false)] at hm
    have hm' : (eA.hom x : P) ∈ map (eA.hom ≫ incl _) (A.bdryFull ⊤) := by
      rw [map_bdryFull, map_hom_incl_top]
      exact hm
    obtain ⟨x', hx', hxx'⟩ := hm'
    rw [ConcreteCategory.comp_apply, incl_apply] at hxx'
    obtain rfl := IsInclusion.injective (f := eA.hom) (Subtype.ext hxx')
    refine ⟨hx', IsInclusion.injective (f := eB.hom) (Subtype.ext ?_)⟩
    rw [apply_mergerGluing, hxy]
  · rw [← hy, apply_mergerGluing]

end Merger

theorem apply_eq_apply_iff_of_isRound (hP : P.IsMolecule) (hM : M.IsMolecule)
    (hrP : P.IsRound ⊤) (hrM : M.IsRound ⊤) (hdP : 0 < krullDim (⊤ : LowerSet P))
    (hdM : 0 < krullDim (⊤ : LowerSet M)) (eA : A ≅ P.restrict (P.bdry ⊤ false))
    (eB : B ≅ P.restrict (P.bdry ⊤ true)) (fA : A ≅ M.restrict (M.bdry ⊤ false))
    (fB : B ≅ M.restrict (M.bdry ⊤ true)) (x : A) (y : B) :
    (eA.hom x : P) = eB.hom y ↔ (fA.hom x : M) = fB.hom y := by
  have he : mergerGluing hP eA eB = mergerGluing hM fA fB :=
    (isSigned_mergerGluing hP eA eB).eq_of_isMolecule
      ((isMoleculeIn_map_iff (eA.hom ≫ incl _) ⊤).1 (by
        rw [map_hom_incl_top]
        exact hP.bdry hdP false))
      (isSigned_mergerGluing hM fA fB)
  rw [apply_eq_apply_iff_mergerGluing hP eA eB hrP hdP,
    apply_eq_apply_iff_mergerGluing hM fA fB hrM hdM, he]

end Atoms.Molecule.OGP
