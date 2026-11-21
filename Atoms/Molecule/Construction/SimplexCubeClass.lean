import Atoms.Molecule.Construction.GrayProductMonoidal
import Atoms.Molecule.Construction.SimplexMaps
import Atoms.Molecule.Construction.ThetaClassification

universe u

open CategoryTheory MonoidalCategory Order

namespace Atoms.Molecule.OGP

open SuspCarrier

private theorem krullDim_top_eq_of_iso {P Q : OGP.{u}} (e : P ≅ Q) :
    krullDim (⊤ : LowerSet P) = krullDim (⊤ : LowerSet Q) := by
  rw [← krullDim_map e.hom ⊤, map_top_of_isIso]

theorem krullDim_simplex (n : ℕ) : krullDim (simplex.{u} n) = n := by
  refine le_antisymm (krullDim_le_coe_iff.2 fun x => ?_) ?_
  · have h := card_simplexVertices n x
    have h' := (simplexVertices n x).card_le_univ
    rw [Fintype.card_fin] at h'
    omega
  · obtain ⟨x, hx⟩ := exists_simplexVertices_eq n Finset.univ Finset.univ_nonempty
    have h := card_simplexVertices n x
    rw [hx, Finset.card_univ, Fintype.card_fin, Nat.add_right_cancel_iff] at h
    exact (congrArg Nat.cast h).le.trans (grade_le_krullDim x)

theorem krullDim_cube (n : ℕ) : krullDim (cube.{u} n) = n := by
  induction n with
  | zero => exact krullDim_globe 0
  | succ n ih => exact (krullDim_grayProduct (krullDim_globe 1) ih).trans (by rw [Nat.add_comm])

inductive IsOrientedSimplex : OGP.{u} → Prop
  | point : IsOrientedSimplex point
  | iso {P Q : OGP.{u}} (e : P ≅ Q) (hP : IsOrientedSimplex P) : IsOrientedSimplex Q
  | cone {P : OGP.{u}} (hP : IsOrientedSimplex P) : IsOrientedSimplex (join point P)

theorem isOrientedSimplex_simplex (n : ℕ) : IsOrientedSimplex (simplex.{u} n) := by
  induction n with
  | zero => exact .point
  | succ n ih => exact .cone ih

theorem isOrientedSimplex_iff {P : OGP.{u}} :
    IsOrientedSimplex P ↔ ∃ n : ℕ, Nonempty (P ≅ simplex.{u} n) := by
  refine ⟨fun h => ?_, fun ⟨n, ⟨e⟩⟩ => .iso e.symm (isOrientedSimplex_simplex n)⟩
  induction h with
  | point => exact ⟨0, ⟨Iso.refl _⟩⟩
  | iso e _ ih =>
    obtain ⟨n, ⟨f⟩⟩ := ih
    exact ⟨n, ⟨e.symm ≪≫ f⟩⟩
  | cone _ ih =>
    obtain ⟨n, ⟨f⟩⟩ := ih
    exact ⟨n + 1, ⟨join.mapIso (Iso.refl point) f⟩⟩

theorem IsOrientedSimplex.isAtom {P : OGP.{u}} (h : IsOrientedSimplex P) : P.IsAtom := by
  obtain ⟨n, ⟨e⟩⟩ := isOrientedSimplex_iff.1 h
  exact (isAtom_iff_of_iso e).2 (isAtom_simplex n)

theorem IsOrientedSimplex.nonempty_iso {P : OGP.{u}} (h : IsOrientedSimplex P) :
    ∃ n : ℕ, krullDim (⊤ : LowerSet P) = n ∧ Nonempty (P ≅ simplex.{u} n) := by
  obtain ⟨n, ⟨e⟩⟩ := isOrientedSimplex_iff.1 h
  exact ⟨n, by rw [krullDim_top_eq_of_iso e, LowerSet.krullDim_top, krullDim_simplex], ⟨e⟩⟩

theorem IsOrientedSimplex.subsingleton_iso {P : OGP.{u}} (h : IsOrientedSimplex P) (n : ℕ) :
    Subsingleton (P ≅ simplex.{u} n) :=
  IsMolecule.subsingleton_iso h.isAtom.isMoleculeIn

def simplexJoinIso : (m n : ℕ) → join (simplex.{u} m) (simplex.{u} n) ≅ simplex.{u} (m + n + 1)
  | 0, n => eqToIso (congrArg (fun k => simplex.{u} (k + 1)) (Nat.zero_add n).symm)
  | m + 1, n => joinAssoc point (simplex m) (simplex n) ≪≫
      join.mapIso (Iso.refl point) (simplexJoinIso m n) ≪≫
      eqToIso (congrArg (fun k => simplex.{u} (k + 1)) (Nat.succ_add m n).symm)

theorem IsOrientedSimplex.join {P Q : OGP.{u}} (hP : IsOrientedSimplex P)
    (hQ : IsOrientedSimplex Q) : IsOrientedSimplex (join P Q) := by
  obtain ⟨m, ⟨e⟩⟩ := isOrientedSimplex_iff.1 hP
  obtain ⟨n, ⟨f⟩⟩ := isOrientedSimplex_iff.1 hQ
  exact .iso (join.mapIso e f ≪≫ simplexJoinIso m n).symm (isOrientedSimplex_simplex _)

theorem IsOrientedSimplex.induction_join {C : OGP.{u} → Prop}
    (iso : ∀ {P Q : OGP.{u}}, (P ≅ Q) → C P → C Q) (point : C OGP.point)
    (join : ∀ {P Q : OGP.{u}}, C P → C Q → C (OGP.join P Q)) {P : OGP.{u}}
    (h : IsOrientedSimplex P) : C P := by
  induction h with
  | point => exact point
  | iso e _ ih => exact iso e ih
  | cone _ ih => exact join point ih

private theorem forall_restrict_Iic_of_iso {C : OGP.{u} → Prop}
    (hC : ∀ {P Q : OGP.{u}}, (P ≅ Q) → C P → C Q) {P Q : OGP.{u}} (e : P ≅ Q)
    (h : ∀ x : P, C (P.restrict (LowerSet.Iic x))) (y : Q) : C (Q.restrict (LowerSet.Iic y)) := by
  obtain ⟨f, -⟩ := exists_iso_restrict_map e.hom (LowerSet.Iic (e.inv y))
  exact hC (f ≪≫ restrictCongr (by rw [map_Iic, Iso.inv_hom_id_apply])) (h (e.inv y))

private theorem nonempty_iso_restrict_Iic_simplex (n : ℕ) (x : simplex.{u} n) :
    Nonempty (simplex.{u} (grade ℕ x) ≅ (simplex.{u} n).restrict (LowerSet.Iic x)) := by
  obtain ⟨f, hf, hfS⟩ : ∃ f : Fin (grade ℕ x + 1) →o Fin (n + 1),
      Function.Injective f ∧ Finset.univ.image f = simplexVertices n x :=
    let f := (simplexVertices n x).orderEmbOfFin (card_simplexVertices n x)
    ⟨f, f.injective, Finset.image_orderEmbOfFin_univ _ (card_simplexVertices n x)⟩
  obtain ⟨t, ht⟩ := exists_simplexVertices_eq (grade ℕ x) Finset.univ Finset.univ_nonempty
  have htop : (⊤ : LowerSet (simplex.{u} (grade ℕ x))) = LowerSet.Iic t :=
    SetLike.ext fun y => iff_of_true LowerSet.mem_top
      ((simplexVertices_subset_iff _).1 (ht ▸ Finset.subset_univ _))
  have hfx : simplex.mapOfInjective.{u} f hf t = x := by
    rw [simplex.mapOfInjective_apply, simplexMap_eq_iff, ht, hfS]
  obtain ⟨e, -⟩ := exists_iso_restrict (simplex.mapOfInjective.{u} f hf)
    (C := LowerSet.Iic x) (by rw [htop, map_Iic, hfx])
  exact ⟨e⟩

theorem IsOrientedSimplex.restrict_Iic {P : OGP.{u}} (h : IsOrientedSimplex P) (x : P) :
    IsOrientedSimplex (P.restrict (LowerSet.Iic x)) := by
  obtain ⟨n, ⟨e⟩⟩ := isOrientedSimplex_iff.1 h
  refine forall_restrict_Iic_of_iso (fun e h => .iso e h) e.symm (fun y => ?_) x
  obtain ⟨f⟩ := nonempty_iso_restrict_Iic_simplex n y
  exact .iso f (isOrientedSimplex_simplex _)

private def dualPointIso (J : ℕ → Bool) : dual point.{u} J ≅ point.{u} :=
  isoMk (OrderIso.refl _) fun {x _} h => ((isMin_point x).not_lt h.lt).elim

private theorem IsOrientedSimplex.nonempty_join_comm {P Q : OGP.{u}} (hP : IsOrientedSimplex P)
    (hQ : IsOrientedSimplex Q) : Nonempty (OGP.join P Q ≅ OGP.join Q P) := by
  obtain ⟨m, ⟨e⟩⟩ := isOrientedSimplex_iff.1 hP
  obtain ⟨n, ⟨f⟩⟩ := isOrientedSimplex_iff.1 hQ
  exact ⟨join.mapIso e f ≪≫ simplexJoinIso m n ≪≫ eqToIso (by rw [Nat.add_comm m n]) ≪≫
    (simplexJoinIso n m).symm ≪≫ (join.mapIso f e).symm⟩

theorem IsOrientedSimplex.dual_bodd {P : OGP.{u}} (h : IsOrientedSimplex P) :
    IsOrientedSimplex (dual P Nat.bodd) ∧ Nonempty (dual P Nat.bodd ≅ P) := by
  obtain ⟨hP, ⟨e⟩⟩ := h.induction_join
    (C := fun P => IsOrientedSimplex P ∧ Nonempty (dual P Nat.bodd ≅ P))
    (fun e ⟨hP, ⟨f⟩⟩ => ⟨.iso e hP, ⟨(dualFunctor Nat.bodd).mapIso e.symm ≪≫ f ≪≫ e⟩⟩)
    ⟨.point, ⟨dualPointIso _⟩⟩
    (fun ⟨hP, ⟨f⟩⟩ ⟨hQ, ⟨g⟩⟩ => by
      obtain ⟨c⟩ := hQ.nonempty_join_comm hP
      exact ⟨hP.join hQ, ⟨joinSwap _ _ ≪≫ join.mapIso g f ≪≫ c⟩⟩)
  exact ⟨.iso e.symm hP, ⟨e⟩⟩

inductive IsOrientedCube : OGP.{u} → Prop
  | point : IsOrientedCube point
  | iso {P Q : OGP.{u}} (e : P ≅ Q) (hP : IsOrientedCube P) : IsOrientedCube Q
  | cylinder {P : OGP.{u}} (hP : IsOrientedCube P) : IsOrientedCube (grayProduct (globe 1) P)

theorem isOrientedCube_cube (n : ℕ) : IsOrientedCube (cube.{u} n) := by
  induction n with
  | zero => exact .point
  | succ n ih => exact .cylinder ih

private theorem isOrientedCube_globe_one : IsOrientedCube (globe.{u} 1) :=
  .iso (grayProductRightUnitor (globe 1)) (isOrientedCube_cube 1)

theorem isOrientedCube_iff {P : OGP.{u}} :
    IsOrientedCube P ↔ ∃ n : ℕ, Nonempty (P ≅ cube.{u} n) := by
  refine ⟨fun h => ?_, fun ⟨n, ⟨e⟩⟩ => .iso e.symm (isOrientedCube_cube n)⟩
  induction h with
  | point => exact ⟨0, ⟨Iso.refl _⟩⟩
  | iso e _ ih =>
    obtain ⟨n, ⟨f⟩⟩ := ih
    exact ⟨n, ⟨e.symm ≪≫ f⟩⟩
  | cylinder _ ih =>
    obtain ⟨n, ⟨f⟩⟩ := ih
    exact ⟨n + 1, ⟨tensorIso (Iso.refl (globe 1)) f⟩⟩

theorem IsOrientedCube.isAtom {P : OGP.{u}} (h : IsOrientedCube P) : P.IsAtom := by
  obtain ⟨n, ⟨e⟩⟩ := isOrientedCube_iff.1 h
  exact (isAtom_iff_of_iso e).2 (isAtom_cube n)

theorem IsOrientedCube.nonempty_iso {P : OGP.{u}} (h : IsOrientedCube P) :
    ∃ n : ℕ, krullDim (⊤ : LowerSet P) = n ∧ Nonempty (P ≅ cube.{u} n) := by
  obtain ⟨n, ⟨e⟩⟩ := isOrientedCube_iff.1 h
  exact ⟨n, by rw [krullDim_top_eq_of_iso e, LowerSet.krullDim_top, krullDim_cube], ⟨e⟩⟩

theorem IsOrientedCube.subsingleton_iso {P : OGP.{u}} (h : IsOrientedCube P) (n : ℕ) :
    Subsingleton (P ≅ cube.{u} n) :=
  IsMolecule.subsingleton_iso h.isAtom.isMoleculeIn

def cubeGrayProductIso : (m n : ℕ) → grayProduct (cube.{u} m) (cube.{u} n) ≅ cube.{u} (m + n)
  | 0, n => grayProductLeftUnitor (cube n) ≪≫ eqToIso (congrArg cube.{u} (Nat.zero_add n).symm)
  | m + 1, n => grayProductAssoc (globe 1) (cube m) (cube n) ≪≫
      tensorIso (Iso.refl (globe 1)) (cubeGrayProductIso m n) ≪≫
      eqToIso (congrArg cube.{u} (Nat.succ_add m n).symm)

theorem IsOrientedCube.grayProduct {P Q : OGP.{u}} (hP : IsOrientedCube P)
    (hQ : IsOrientedCube Q) : IsOrientedCube (grayProduct P Q) := by
  obtain ⟨m, ⟨e⟩⟩ := isOrientedCube_iff.1 hP
  obtain ⟨n, ⟨f⟩⟩ := isOrientedCube_iff.1 hQ
  exact .iso (tensorIso e f ≪≫ cubeGrayProductIso m n).symm (isOrientedCube_cube _)

theorem IsOrientedCube.induction_grayProduct {C : OGP.{u} → Prop}
    (iso : ∀ {P Q : OGP.{u}}, (P ≅ Q) → C P → C Q) (point : C OGP.point)
    (arrow : C (globe 1)) (gray : ∀ {P Q : OGP.{u}}, C P → C Q → C (OGP.grayProduct P Q))
    {P : OGP.{u}}
    (h : IsOrientedCube P) : C P := by
  induction h with
  | point => exact point
  | iso e _ ih => exact iso e ih
  | cylinder _ ih => exact gray arrow ih

private theorem nonempty_dual_globe_one_iso (J : ℕ → Bool) :
    Nonempty (dual (globe.{u} 1) J ≅ globe.{u} 1) := by
  obtain ⟨n, ⟨e⟩⟩ := IsGlobe.dual ⟨1, ⟨Iso.refl (globe.{u} 1)⟩⟩ J
  have h := krullDim_top_eq_of_iso e
  rw [LowerSet.krullDim_top, LowerSet.krullDim_top, krullDim_globe, krullDim_globe] at h
  obtain rfl : n = 1 := by exact_mod_cast h.symm
  exact ⟨e⟩

private theorem IsOrientedCube.nonempty_grayProduct_comm {P Q : OGP.{u}}
    (hP : IsOrientedCube P) (hQ : IsOrientedCube Q) :
    Nonempty (OGP.grayProduct P Q ≅ OGP.grayProduct Q P) := by
  obtain ⟨m, ⟨e⟩⟩ := isOrientedCube_iff.1 hP
  obtain ⟨n, ⟨f⟩⟩ := isOrientedCube_iff.1 hQ
  exact ⟨tensorIso e f ≪≫ cubeGrayProductIso m n ≪≫ eqToIso (by rw [Nat.add_comm m n]) ≪≫
    (cubeGrayProductIso n m).symm ≪≫ (tensorIso f e).symm⟩

theorem IsOrientedCube.dual_bodd {P : OGP.{u}} (h : IsOrientedCube P) :
    IsOrientedCube (dual P Nat.bodd) ∧ Nonempty (dual P Nat.bodd ≅ P) := by
  obtain ⟨hP, ⟨e⟩⟩ := h.induction_grayProduct
    (C := fun P => IsOrientedCube P ∧ Nonempty (dual P Nat.bodd ≅ P))
    (fun e ⟨hP, ⟨f⟩⟩ => ⟨.iso e hP, ⟨(dualFunctor Nat.bodd).mapIso e.symm ≪≫ f ≪≫ e⟩⟩)
    ⟨.point, ⟨dualPointIso _⟩⟩ ⟨isOrientedCube_globe_one, nonempty_dual_globe_one_iso _⟩
    (fun ⟨hP, ⟨f⟩⟩ ⟨hQ, ⟨g⟩⟩ => by
      obtain ⟨c⟩ := hQ.nonempty_grayProduct_comm hP
      exact ⟨hP.grayProduct hQ, ⟨grayProductSwap _ _ ≪≫ tensorIso g f ≪≫ c⟩⟩)
  exact ⟨.iso e.symm hP, ⟨e⟩⟩

private theorem isOrientedCube_restrict_Iic_globe_one (a : globe.{u} 1) :
    IsOrientedCube ((globe.{u} 1).restrict (LowerSet.Iic a)) := by
  rcases a with α | ⟨⟨⟩⟩
  · exact .iso (isoPointRestrictIic (isMin_pole α)) .point
  · obtain ⟨e⟩ := nonempty_iso_restrict_top (globe.{u} 1)
    exact .iso (e ≪≫ restrictCongr LowerSet.Iic_top.symm) isOrientedCube_globe_one

theorem IsOrientedCube.restrict_Iic {P : OGP.{u}} (h : IsOrientedCube P) (x : P) :
    IsOrientedCube (P.restrict (LowerSet.Iic x)) := by
  induction h with
  | point => exact .iso (isoPointRestrictIic (isMin_point x)) .point
  | iso e _ ih => exact forall_restrict_Iic_of_iso (fun e h => .iso e h) e ih x
  | cylinder _ ih =>
    obtain ⟨a, b⟩ := x
    exact .iso (grayProductClosureIso a b).symm
      ((isOrientedCube_restrict_Iic_globe_one a).grayProduct (ih b))

def grayProductDualTopIso (P Q : OGP.{u}) :
    dual (grayProduct P Q) ⊤ ≅ grayProduct (dual P ⊤) (dual Q ⊤) :=
  isoMk (OrderIso.refl _) fun {p q} h => by
    rcases p with ⟨x, y⟩
    rcases q with ⟨x', y'⟩
    rcases Prod.covBy_iff.1 h with ⟨hx, hyy⟩ | ⟨hy, hxx⟩
    · obtain rfl : y' = y := hyy
      replace hx : x' ⋖ x := hx
      have h' : ((x', y') : grayProduct (dual P ⊤) (dual Q ⊤)) ⋖ (x, y') :=
        Prod.covBy_iff.2 (.inl ⟨hx, rfl⟩)
      rw [orient_congr _ _ _ h', grayProduct_orient_of_covBy_fst (P := dual P ⊤)
        (Q := dual Q ⊤) hx y', orient_dual, orient_dual, grayProduct_orient_of_covBy_fst hx y' h]
      all_goals rfl
    · obtain rfl : x' = x := hxx
      replace hy : y' ⋖ y := hy
      have h' : ((x', y') : grayProduct (dual P ⊤) (dual Q ⊤)) ⋖ (x', y) :=
        Prod.covBy_iff.2 (.inr ⟨hy, rfl⟩)
      rw [orient_congr _ _ _ h', grayProduct_orient_of_covBy_snd (P := dual P ⊤)
        (Q := dual Q ⊤) x' hy, orient_dual, orient_dual, grayProduct_orient_of_covBy_snd x' hy h]
      · exact Bool.xor_left_comm _ _ _
      all_goals rfl

private theorem IsOrientedCube.nonempty_dual_top_iso {P : OGP.{u}} (h : IsOrientedCube P) :
    Nonempty (OGP.dual P ⊤ ≅ P) := by
  induction h with
  | point => exact ⟨dualPointIso ⊤⟩
  | iso e _ ih =>
    obtain ⟨f⟩ := ih
    exact ⟨(dualFunctor ⊤).mapIso e.symm ≪≫ f ≪≫ e⟩
  | cylinder _ ih =>
    obtain ⟨f⟩ := ih
    obtain ⟨g⟩ := nonempty_dual_globe_one_iso.{u} ⊤
    exact ⟨grayProductDualTopIso _ _ ≪≫ tensorIso g f⟩

private def dualDualIsoOfForall (P : OGP.{u}) {J K L : ℕ → Bool}
    (h : ∀ n, 0 < n → J n = xor (K n) (L n)) : OGP.dual P J ≅ OGP.dual (OGP.dual P K) L :=
  isoMk (OrderIso.refl P) fun {x _} hc => by
    have hx : 0 < grade ℕ x := Nat.zero_lt_of_lt (grade_strictMono hc.lt)
    simp only [OrderIso.refl_apply]
    rw [h _ hx, Bool.xor_assoc]
    exact Bool.xor_left_comm _ _ _

theorem IsOrientedCube.dual {P : OGP.{u}} (h : IsOrientedCube P) {J : ℕ → Bool}
    (hJ : ∃ a b : Bool, ∀ n, 0 < n → J n = xor (a && n.bodd) b) :
    IsOrientedCube (OGP.dual P J) ∧ Nonempty (OGP.dual P J ≅ P) := by
  obtain ⟨a, b, hab⟩ := hJ
  have hK : IsOrientedCube (OGP.dual P fun n => a && n.bodd) ∧
      Nonempty (OGP.dual P (fun n => a && n.bodd) ≅ P) := by
    cases a
    · exact ⟨.iso (dualIsoOfForall _ P fun _ => rfl).symm h,
        ⟨dualIsoOfForall _ P fun _ => rfl⟩⟩
    · exact h.dual_bodd
  obtain ⟨hQ, ⟨f⟩⟩ := hK
  have hL : Nonempty (OGP.dual (OGP.dual P fun n => a && n.bodd) (fun _ => b) ≅
      OGP.dual P fun n => a && n.bodd) := by
    cases b
    · exact ⟨dualIsoOfForall _ _ fun _ => rfl⟩
    · exact hQ.nonempty_dual_top_iso
  obtain ⟨g⟩ := hL
  have e := dualDualIsoOfForall P hab ≪≫ g ≪≫ f
  exact ⟨.iso e.symm h, ⟨e⟩⟩

end Atoms.Molecule.OGP
