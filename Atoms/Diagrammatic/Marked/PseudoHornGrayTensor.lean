import Atoms.Diagrammatic.Marked.Entire
import Atoms.Diagrammatic.Marked.HornGrayTensor
import Atoms.Diagrammatic.Marked.PseudoGrayComparison

open CategoryTheory Limits Opposite HomotopicalAlgebra Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Shape.MarkedHornData

def withMarking (m : MarkedHornData) (B : Set m.atom.ogp) (hB : m.marking ⊆ B)
    (hB' : ∀ a ∈ B, a ∈ m.hornSet ∧ 0 < grade ℕ a) : MarkedHornData :=
  { m with
    marking := B
    marking_mem := hB'
    marked_tops := fun i hi y hy hyd => hB (m.marked_tops i hi y hy hyd) }

theorem targetMarking_withMarking (m : MarkedHornData) {B : Set m.atom.ogp} (hB : m.marking ⊆ B)
    (hB' : ∀ a ∈ B, a ∈ m.hornSet ∧ 0 < grade ℕ a)
    (hf : m.atom.ogp.faces (!m.side) m.atom.top ⊆ B) :
    (m.withMarking B hB hB').targetMarking = insert m.atom.top (insert m.face B) :=
  Set.ext fun _ => or_congr_right (or_congr_left (and_iff_right hf))

end Atoms.Shape.MarkedHornData

namespace Atoms.Shape.MarkedHornData

open Atoms.Molecule Atoms.Molecule.OGP

variable (h : MarkedHornData) (V : Atom)

def positivePairs : Set (Atom.grayTensor h.atom V).ogp :=
  {w | (((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.hornSet ∨
      ((Atom.grayTensorIso h.atom V).inv w).2 ∈ V.ogp.bdryFull ⊤) ∧
    0 < grade ℕ ((Atom.grayTensorIso h.atom V).inv w).1 ∧
      0 < grade ℕ ((Atom.grayTensorIso h.atom V).inv w).2}

def pseudoGrayTensorRight (marked : Bool) (hV : marked = true → 0 < V.dimension)
    (L R M : ℕ → LowerSet (Atom.grayTensor h.atom V).ogp)
    (staged : (Atom.grayTensor h.atom V).ogp.IsStagedPasting
      ((Atom.grayTensor h.atom V).dimension - 1) (.Iic (h.grayTensorFace V)) L R M)
    (stage_last : M ((Atom.grayTensor h.atom V).dimension - 1) =
      (Atom.grayTensor h.atom V).ogp.bdry ⊤ h.side)
    (tops : ∀ i < (Atom.grayTensor h.atom V).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
      grade ℕ y = i + 1 → y ∈ h.grayTensorMarking V false) : MarkedHornData :=
  (h.grayTensorRight V marked hV L R M staged stage_last tops).withMarking
    (h.grayTensorMarking V marked ∪ h.positivePairs V) Set.subset_union_left fun w hw =>
      hw.elim (h.grayTensorMarking_mem V hV w) fun hw => ⟨h.mem_hornSet_grayTensorFace V hw.1,
        (Nat.add_pos_left hw.2.1 _).trans_eq
          ((isMorphism (Atom.grayTensorIso h.atom V).inv).grade_eq w)⟩

variable {marked : Bool} {hV : marked = true → 0 < V.dimension}
  {L R M : ℕ → LowerSet (Atom.grayTensor h.atom V).ogp}
  {hs : (Atom.grayTensor h.atom V).ogp.IsStagedPasting
    ((Atom.grayTensor h.atom V).dimension - 1) (.Iic (h.grayTensorFace V)) L R M}
  {hM : M ((Atom.grayTensor h.atom V).dimension - 1) = (Atom.grayTensor h.atom V).ogp.bdry ⊤ h.side}
  {ht : ∀ i < (Atom.grayTensor h.atom V).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
    grade ℕ y = i + 1 → y ∈ h.grayTensorMarking V false}

theorem mem_targetMarking_pseudoGrayTensorRight_iff (hU : 2 ≤ h.atom.dimension)
    (hV' : 0 < V.dimension) {w : (Atom.grayTensor h.atom V).ogp} :
    w ∈ (h.pseudoGrayTensorRight V marked hV L R M hs hM ht).targetMarking ↔
      (((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.targetMarking ∨
        (marked = true ∧ ((Atom.grayTensorIso h.atom V).inv w).2 = V.top)) ∨
      0 < grade ℕ ((Atom.grayTensorIso h.atom V).inv w).1 ∧
        0 < grade ℕ ((Atom.grayTensorIso h.atom V).inv w).2 := by
  have hgrade (z : (Atom.grayTensor h.atom V).ogp) :
      grade ℕ ((Atom.grayTensorIso h.atom V).inv z).1 +
          grade ℕ ((Atom.grayTensorIso h.atom V).inv z).2 = grade ℕ z ∧
        grade ℕ ((Atom.grayTensorIso h.atom V).inv z).1 ≤ h.atom.dimension ∧
          grade ℕ ((Atom.grayTensorIso h.atom V).inv z).2 ≤ V.dimension := by
    rw [h.atom.dimension_eq, V.dimension_eq]
    exact ⟨(isMorphism (Atom.grayTensorIso h.atom V).inv).grade_eq z,
      grade_mono (h.atom.le_top _), grade_mono (V.le_top _)⟩
  have hfaces : (Atom.grayTensor h.atom V).ogp.faces (!h.side) (Atom.grayTensor h.atom V).top ⊆
      h.grayTensorMarking V marked ∪ h.positivePairs V := by
    intro z hz
    have hzh := (h.mem_hornSet_grayTensorRight_iff V).1
      ((h.grayTensorRight V marked hV L R M hs hM ht).mem_hornSet_iff.2
        ⟨((Atom.grayTensor h.atom V).mem_bdryFull_top_iff _).2 hz.1.ne, fun h3 =>
          Set.disjoint_left.1 (disjoint_faces _ h.side) (h.grayTensorFace_mem_faces V)
            (by rw [h3] at hz; exact hz)⟩)
    have hz1 : grade ℕ z + 1 = h.atom.dimension + V.dimension :=
      (Nat.covBy_iff_add_one_eq.1 (hz.1.grade ℕ)).trans
        ((Atom.grayTensor h.atom V).dimension_eq.symm.trans (Atom.dimension_grayTensor _ _))
    obtain ⟨h1, h2, h3⟩ := hgrade z
    by_cases hb : 0 < grade ℕ ((Atom.grayTensorIso h.atom V).inv z).2
    · exact Or.inr ⟨hzh, by omega, hb⟩
    refine Or.inl (Or.inr (Or.inl ⟨h.mem_targetMarking_iff.2 (Or.inl
      (GradeOrder.eq_of_le_of_grade_le (h.atom.le_top _) (by rw [← h.atom.dimension_eq]; omega))),
      (V.mem_bdryFull_top_iff _).2 fun h4 => ?_⟩))
    rw [h4, ← V.dimension_eq] at hb
    omega
  have hinj : Function.Injective (Atom.grayTensorIso h.atom V).inv :=
    Function.LeftInverse.injective (Iso.inv_hom_id_apply _)
  have hT : (h.pseudoGrayTensorRight V marked hV L R M hs hM ht).targetMarking =
      insert (Atom.grayTensor h.atom V).top (insert (h.grayTensorFace V)
        (h.grayTensorMarking V marked ∪ h.positivePairs V)) :=
    targetMarking_withMarking (h.grayTensorRight V marked hV L R M hs hM ht) _ _ hfaces
  refine (Set.ext_iff.1 hT w).trans (Iff.trans ⟨?_, ?_⟩ (or_congr_left
    (h.mem_targetMarking_grayTensorRight_iff V (hV := hV) (L := L) (R := R) (M := M) (hs := hs)
      (hM := hM) (ht := ht))))
  · rintro (rfl | rfl | hw | hw)
    · exact Or.inl (Or.inl rfl)
    · refine Or.inr ?_
      rw [grayTensorFace, Iso.hom_inv_id_apply, ← V.dimension_eq]
      exact ⟨(by have := h.dim_face_add_one; omega : 0 < grade ℕ h.face), hV'⟩
    · exact Or.inl (Or.inr (Or.inr hw))
    · exact Or.inr hw.2
  · rintro (hw | hw)
    · rcases (MarkedHornData.mem_targetMarking_iff _).1 hw with hw | ⟨-, hw⟩ | hw
      · exact Or.inl hw
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (Or.inl hw))
    by_cases hh : ((Atom.grayTensorIso h.atom V).inv w).1 ∈ h.hornSet ∨
      ((Atom.grayTensorIso h.atom V).inv w).2 ∈ V.ogp.bdryFull ⊤
    · exact Or.inr (Or.inr (Or.inr ⟨hh, hw⟩))
    obtain ⟨h1, h2⟩ := not_or.1 hh
    rw [V.mem_bdryFull_top_iff, not_not] at h2
    rw [h.mem_hornSet_iff, h.atom.mem_bdryFull_top_iff, not_and, not_not] at h1
    have hinj : Function.Injective (Atom.grayTensorIso h.atom V).inv :=
      Function.LeftInverse.injective (Iso.inv_hom_id_apply _)
    by_cases h3 : ((Atom.grayTensorIso h.atom V).inv w).1 = h.atom.top
    · exact Or.inl (hinj ((Prod.ext h3 h2).trans (Atom.grayTensorIso_inv_top _ _).symm))
    · exact Or.inr (Or.inl (hinj ((Prod.ext (h1 h3) h2).trans
        (Iso.hom_inv_id_apply (Atom.grayTensorIso h.atom V) (h.face, V.top)).symm)))

end Atoms.Shape.MarkedHornData

namespace Atoms.Diagrammatic

instance mono_sphereToMarkedBall (V : Atom) : Mono (sphereToMarkedBall.{u} V) :=
  (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (sphereInclusion V)))

instance mono_markingToMarkedBall (V : Atom) (hV : 0 < V.dimension) :
    Mono (markingToMarkedBall.{u} V hV) :=
  (MarkedPresheaf.mono_iff _).2 inferInstance

instance mono_markingInclusion (U : Atom) (hU : 0 < U.dimension) :
    Mono (MarkedDiagSet.markingInclusion.{u} U hU) :=
  (MarkedPresheaf.mono_iff _).2 inferInstance

private theorem mem_range_of_isIso_forget {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y)
    [IsIso (MarkedPresheaf.forget.map f)] {U : Atom} (y : diagram Y.underlying U) :
    y ∈ Set.range ((MarkedPresheaf.forget.map f).app (op U)) :=
  ⟨(inv (MarkedPresheaf.forget.map f)).app (op U) y, ConcreteCategory.congr_hom
    (NatTrans.congr_app (IsIso.inv_hom_id (MarkedPresheaf.forget.map f)) (op U)) y⟩

section CobaseChange

variable {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

theorem isPushout_pseudoPushoutProduct
    (h : ∀ (U V : Atom) (y₁ : diagram Y₁.underlying U) (y₂ : diagram Y₂.underlying V),
      0 < U.dimension → 0 < V.dimension → y₁ ∈ Y₁.marked U ∨ y₂ ∈ Y₂.marked V ∨
        y₁ ∈ Set.range ((MarkedPresheaf.forget.map f₁).app (op U)) ∨
        y₂ ∈ Set.range ((MarkedPresheaf.forget.map f₂).app (op V))) :
    IsPushout (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι
      (pushoutObjGrayToPseudo f₁ f₂) (grayToPseudo Y₁ Y₂)
      (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).ι := by
  let F₀ := Functor.curry.obj (markedTensorBifunctor.{u} false)
  let F₁ := Functor.curry.obj (markedTensorBifunctor.{u} true)
  let sq := Functor.PushoutObjObj.ofHasPushout F₁ f₁ f₂
  have w : CommSq (Functor.PushoutObjObj.ofHasPushout F₀ f₁ f₂).ι
      (pushoutObjGrayToPseudo f₁ f₂) (grayToPseudo Y₁ Y₂) sq.ι :=
    ⟨pushoutProduct_comp_grayToPseudo f₁ f₂⟩
  have hF := @IsPushout.of_vert_isIso _ _ _ _ _ _ _ _ _ _
    (isIso_forget_map_pushoutObjGrayToPseudo f₁ f₂) (isIso_forget_map_grayToPseudo Y₁ Y₂)
    (w.map MarkedPresheaf.forget)
  refine IsPushout.of_isColimit' w (MarkedPresheaf.isColimitOfForget _
    ((isColimitMapCoconePushoutCoconeEquiv _ _).symm hF.isColimit) fun T z hz => ?_)
  suffices hs : z ∈ (markedTensor false Y₁ Y₂).marked T ∨
      ∃ x ∈ sq.pt.marked T, (MarkedPresheaf.forget.map sq.ι).app (op T) x = z by
    rcases hs with hz' | ⟨x, hx, hxz⟩
    · exact ⟨WalkingSpan.left, z, hz', rfl⟩
    · exact ⟨WalkingSpan.right, x, hx, hxz⟩
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hd | ⟨U, V, y₁, y₂, e, hm, rfl⟩
  · exact Or.inl ((mem_marked_markedTensor _ _ _ _ _).2 (Or.inl hd))
  have hmask (hm' : tensorMask false Y₁ Y₂ U V y₁ y₂) :
      (grayTensor Y₁.underlying Y₂.underlying).map e.hom.op (grayTensorCell y₁ y₂) ∈
        (markedTensor false Y₁ Y₂).marked T :=
    (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨U, V, y₁, y₂, e, hm', rfl⟩)
  rcases hm with hy | hy | ⟨-, hU, hV⟩
  · exact Or.inl (hmask (Or.inl hy))
  · exact Or.inl (hmask (Or.inr (Or.inl hy)))
  rcases h U V y₁ y₂ hU hV with hy | hy | ⟨x₁, rfl⟩ | ⟨x₂, rfl⟩
  · exact Or.inl (hmask (Or.inl hy))
  · exact Or.inl (hmask (Or.inr (Or.inl hy)))
  · obtain ⟨x, hx, hxz⟩ := exists_mem_marked_ι_eq_of_corner true sq f₁ (𝟙 Y₂) sq.inr sq.inr_ι e
      x₁ y₂ (Or.inr (Or.inr ⟨rfl, hU, hV⟩))
    exact Or.inr ⟨x, hx, hxz.trans (by rw [CategoryTheory.Functor.map_id]; rfl)⟩
  · obtain ⟨x, hx, hxz⟩ := exists_mem_marked_ι_eq_of_corner true sq (𝟙 Y₁) f₂ sq.inl sq.inl_ι e
      y₁ x₂ (Or.inr (Or.inr ⟨rfl, hU, hV⟩))
    exact Or.inr ⟨x, hx, hxz.trans (by rw [CategoryTheory.Functor.map_id]; rfl)⟩

private theorem weakEquivalence_pseudoPushoutProduct_of_forall (n : ℕ∞) [Mono f₁] [Mono f₂]
    (h : ∀ (U V : Atom) (y₁ : diagram Y₁.underlying U) (y₂ : diagram Y₂.underlying V),
      0 < U.dimension → 0 < V.dimension → y₁ ∈ Y₁.marked U ∨ y₂ ∈ Y₂.marked V ∨
        y₁ ∈ Set.range ((MarkedPresheaf.forget.map f₁).app (op U)) ∨
        y₂ ∈ Set.range ((MarkedPresheaf.forget.map f₂).app (op V)))
    (hw : WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).ι) := by
  have : PreservesColimitsOfShape WalkingSpan (MarkedDiagSet.toCoinductive.{u} n) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingSpan (𝟭 MarkedDiagSet.{u}))
  rw [weakEquivalence_iff]
  exact (MorphismProperty.of_isPushout (P := trivialCofibrations (MarkedDiagSet.Coinductive.{u} n))
    ((isPushout_pseudoPushoutProduct f₁ f₂ h).map
    (MarkedDiagSet.toCoinductive n)).flip ⟨mono_markedPushoutProduct f₁ f₂,
      (weakEquivalence_iff _).1 hw⟩).2

end CobaseChange

theorem MarkedDiagSet.Coinductive.weakEquivalence_pseudoPushoutProduct_of_marked_left (n : ℕ∞)
    {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [Mono f₁] [Mono f₂]
    (h : ∀ (U : Atom) (y : diagram Y₁.underlying U), 0 < U.dimension →
      y ∉ Set.range ((MarkedPresheaf.forget.map f₁).app (op U)) → y ∈ Y₁.marked U)
    (hw : WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).ι) :=
  weakEquivalence_pseudoPushoutProduct_of_forall f₁ f₂ n (fun U _ y₁ _ hU _ =>
    (em (y₁ ∈ Set.range _)).elim (Or.inr ∘ Or.inr ∘ Or.inl) (Or.inl ∘ h U y₁ hU)) hw

theorem MarkedDiagSet.Coinductive.weakEquivalence_pseudoPushoutProduct_of_marked_right (n : ℕ∞)
    {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [Mono f₁] [Mono f₂]
    (h : ∀ (U : Atom) (y : diagram Y₂.underlying U), 0 < U.dimension →
      y ∉ Set.range ((MarkedPresheaf.forget.map f₂).app (op U)) → y ∈ Y₂.marked U)
    (hw : WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι)) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).ι) :=
  weakEquivalence_pseudoPushoutProduct_of_forall f₁ f₂ n (fun _ V _ y₂ _ hV =>
    (em (y₂ ∈ Set.range _)).elim (Or.inr ∘ Or.inr ∘ Or.inr) (Or.inr ∘ Or.inl ∘ h V y₂ hV)) hw

theorem MarkedDiagSet.Coinductive.weakEquivalence_pseudoPushoutProduct_markingInclusion_sphere
    (n : ℕ∞) (U V : Atom) (hU : 0 < U.dimension) (hn : n < U.dimension) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true))
      (MarkedDiagSet.markingInclusion U hU) (sphereToMarkedBall V)).ι) :=
  weakEquivalence_pseudoPushoutProduct_of_marked_left n _ _
    (fun _ y _ hy => absurd (mem_range_of_isIso_forget _ y) hy)
    (weakEquivalence_pushoutProduct_markingInclusion_sphere n U V hU hn)

theorem MarkedDiagSet.Coinductive.weakEquivalence_pseudoPushoutProduct_sphere_markingInclusion
    (n : ℕ∞) (U V : Atom) (hU : 0 < U.dimension) (hn : n < U.dimension) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true))
      (sphereToMarkedBall V) (MarkedDiagSet.markingInclusion U hU)).ι) :=
  weakEquivalence_pseudoPushoutProduct_of_marked_right n _ _
    (fun _ y _ hy => absurd (mem_range_of_isIso_forget _ y) hy)
    (weakEquivalence_pushoutProduct_sphere_markingInclusion n U V hU hn)

section HornSphere

open Atoms.Molecule Atoms.Molecule.OGP

variable (h : MarkedHornData) (V : Atom) (marked : Bool) (hV : marked = true → 0 < V.dimension)
  (L R S : ℕ → LowerSet (Atom.grayTensor h.atom V).ogp)
  (hs : (Atom.grayTensor h.atom V).ogp.IsStagedPasting
    ((Atom.grayTensor h.atom V).dimension - 1) (.Iic (h.grayTensorFace V)) L R S)
  (hS : S ((Atom.grayTensor h.atom V).dimension - 1) = (Atom.grayTensor h.atom V).ogp.bdry ⊤ h.side)
  (ht : ∀ i < (Atom.grayTensor h.atom V).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
    grade ℕ y = i + 1 → y ∈ h.grayTensorMarking V false)
  {M : Set V.ogp} {hM : ∀ z ∈ M, 0 < grade ℕ z}

variable {h V marked hV L R S hs hS ht} in
private theorem arrowIso_hom_right_app_map_grayTensorCell
    {f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM}
    (E : Arrow.mk (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι) ≅
      Arrow.mk (MarkedPresheaf.forget.map (markedHornInclusion.{u}
        (h.pseudoGrayTensorRight V marked hV L R S hs hS ht))))
    {T A B : Atom} (f : T ⟶ Atom.grayTensor A B) (c : h.target.underlying.obj (op A))
    (d : (ball.{u} V).obj (op B)) :
    (E.hom.right.app (op T) ((grayTensor _ _).map f.op (grayTensorCell c d))).1 =
      ULift.up (f ≫ Atom.grayTensorMap c.1.down d.down) := by
  have hR : E.hom.right ≫ (closedSubpresheafUnivIso _).hom = (tensorBallIso h V).hom :=
    congrArg Iso.hom (iso_ball_ext (Arrow.rightFunc.mapIso E ≪≫ closedSubpresheafUnivIso _)
      (tensorBallIso h V))
  exact (congrFun (congrArg (fun φ => (NatTrans.app φ (op T) : _ → _)) hR) _).trans
    (tensorBallIso_hom_app h V f c d)

variable {h V marked hV L R S hs hS ht} in
private theorem grayTensorIso_inv_arrowIso_hom_right_app_top
    {f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM}
    (E : Arrow.mk (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι) ≅
      Arrow.mk (MarkedPresheaf.forget.map (markedHornInclusion.{u}
        (h.pseudoGrayTensorRight V marked hV L R S hs hS ht))))
    {T A B : Atom} (e : T ≅ Atom.grayTensor A B) (c : h.target.underlying.obj (op A))
    (d : (ball.{u} V).obj (op B)) :
    (Atom.grayTensorIso h.atom V).inv (ConcreteCategory.hom (E.hom.right.app (op T)
      ((grayTensor _ _).map e.hom.op (grayTensorCell c d))).1.down T.top) =
        (ConcreteCategory.hom c.1.down A.top, ConcreteCategory.hom d.down B.top) := by
  rw [arrowIso_hom_right_app_map_grayTensorCell E]
  change (Atom.grayTensorIso h.atom V).inv (Atom.grayTensorMap c.1.down d.down (e.hom T.top)) = _
  rw [iso_hom_apply_top, Atom.grayTensorIso_inv_grayTensorMap_top]

variable {h V marked hV L R S hs hS ht} in
private theorem isDegenerate_arrowIso_hom_right_app_iff
    {f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM}
    (E : Arrow.mk (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι) ≅
      Arrow.mk (MarkedPresheaf.forget.map (markedHornInclusion.{u}
        (h.pseudoGrayTensorRight V marked hV L R S hs hS ht))))
    {W : Atom} (y : (grayTensor h.target.underlying (ball.{u} V)).obj (op W)) :
    IsDegenerate (ball.{u} _) (E.hom.right.app (op W) y).1 ↔
      IsDegenerate (grayTensor h.target.underlying (ball.{u} V)) y :=
  let e' := Arrow.rightFunc.mapIso E ≪≫ closedSubpresheafUnivIso _
  ⟨fun hy => Iso.hom_inv_id_app_apply e' (op W) y ▸ isDegenerate_app e'.inv hy,
    isDegenerate_app e'.hom⟩

variable {h V marked hV L R S hs hS ht} in
private theorem mem_marked_markedTensor_of_not_isDegenerate (hU : 2 ≤ h.atom.dimension)
    (hV' : 0 < V.dimension) (hMm : ∀ b, b ∈ M ↔ marked = true ∧ b = V.top)
    {f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM}
    (E : Arrow.mk (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι) ≅
      Arrow.mk (MarkedPresheaf.forget.map (markedHornInclusion.{u}
        (h.pseudoGrayTensorRight V marked hV L R S hs hS ht))))
    {W : Atom} {y : (grayTensor h.target.underlying (ball.{u} V)).obj (op W)}
    (hdeg : ¬IsDegenerate (grayTensor h.target.underlying (ball.{u} V)) y)
    (hy : ConcreteCategory.hom (E.hom.right.app (op W) y).1.down W.top ∈
      (h.pseudoGrayTensorRight V marked hV L R S hs hS ht).targetMarking) :
    y ∈ (markedTensor true h.target (markedBall.{u} V M hM)).marked W := by
  refine (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ?_)
  have hEinj : Function.Injective (E.hom.right.app (op W)) :=
    Function.LeftInverse.injective fun y => Iso.hom_inv_id_app_apply (Arrow.rightFunc.mapIso E) _ y
  set g : W ⟶ Atom.grayTensor h.atom V := (E.hom.right.app (op W) y).1.down with hg
  obtain ⟨W₀, p, i, hp, hi, hpi⟩ := exists_collapse_inclusion_factorization g
  have hpiso : IsIso p := by
    by_contra hni
    exact hdeg ((isDegenerate_arrowIso_hom_right_app_iff E y).1
      ⟨W₀, p, ULift.up i, hp, hni, congrArg ULift.up hpi⟩)
  have : Mono g := by
    have := mono_of_isInclusionHom i hi
    exact hpi ▸ mono_comp p i
  obtain ⟨A, B, i', j', e, -, -, he⟩ :=
    Atom.exists_iso_comp_grayTensorMap_of_isInclusionHom g (isInclusionHom_of_mono g)
  let c : h.target.underlying.obj (op A) := ⟨ULift.up i', fun _ => LowerSet.mem_top⟩
  have hy' : y = (grayTensor _ _).map e.hom.op (grayTensorCell c (ULift.up j')) := by
    exact hEinj (Subtype.ext ((congrArg ULift.up he.symm).trans
      (arrowIso_hom_right_app_map_grayTensorCell E e.hom c (ULift.up j')).symm))
  have hpair : (Atom.grayTensorIso h.atom V).inv (ConcreteCategory.hom g W.top) =
      (ConcreteCategory.hom i' A.top, ConcreteCategory.hom j' B.top) := by
    rw [← he]
    change (Atom.grayTensorIso h.atom V).inv (Atom.grayTensorMap i' j' (e.hom W.top)) = _
    rw [iso_hom_apply_top, Atom.grayTensorIso_inv_grayTensorMap_top]
  have h1 := (h.mem_targetMarking_pseudoGrayTensorRight_iff V (hV := hV) (L := L) (R := R) (M := S)
    (hs := hs) (hM := hS) (ht := ht) hU hV' (w := ConcreteCategory.hom g W.top)).1 hy
  rw [hpair] at h1
  refine ⟨A, B, c, ULift.up j', e, ?_, hy'⟩
  rcases h1 with (h1 | ⟨hm, h2⟩) | ⟨h1, h2⟩
  · exact Or.inl ((mem_marked_markedClosedSubset_univ_iff _ _ _ _).2 (Or.inr h1))
  · exact Or.inr (Or.inl ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
      (Or.inr ((hMm _).2 ⟨hm, h2⟩))))
  · exact Or.inr (Or.inr ⟨rfl, h1.trans_le (grade_apply_top_le i'),
      h2.trans_le (grade_apply_top_le j')⟩)

variable {h V marked hV L R S hs hS ht} in
private theorem mem_marked_markedTensor_iff_arrowIso (hU : 2 ≤ h.atom.dimension)
    (hV' : 0 < V.dimension) (hMm : ∀ b, b ∈ M ↔ marked = true ∧ b = V.top)
    {f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM}
    (E : Arrow.mk (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι) ≅
      Arrow.mk (MarkedPresheaf.forget.map (markedHornInclusion.{u}
        (h.pseudoGrayTensorRight V marked hV L R S hs hS ht))))
    (W : Atom) (y : (grayTensor h.target.underlying (ball.{u} V)).obj (op W)) :
    y ∈ (markedTensor true h.target (markedBall.{u} V M hM)).marked W ↔
      E.hom.right.app (op W) y ∈
        (h.pseudoGrayTensorRight V marked hV L R S hs hS ht).target.marked W := by
  have hEd {W : Atom} (y : (grayTensor h.target.underlying (ball.{u} V)).obj (op W)) :=
    isDegenerate_arrowIso_hom_right_app_iff E y
  have htopv {T A B : Atom} (e : T ≅ Atom.grayTensor A B) (c : h.target.underlying.obj (op A))
      (d : (ball.{u} V).obj (op B)) := grayTensorIso_inv_arrowIso_hom_right_app_top E e c d
  have hT (w : (Atom.grayTensor h.atom V).ogp) := h.mem_targetMarking_pseudoGrayTensorRight_iff V
    (hV := hV) (L := L) (R := R) (M := S) (hs := hs) (hM := hS) (ht := ht) hU hV' (w := w)
  refine (mem_marked_markedTensor _ _ _ _ _).trans
    (Iff.trans ?_ (mem_marked_markedClosedSubset_univ_iff _ _ _ _).symm)
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · rcases hy with hy | ⟨A, B, c, d, e, hm, rfl⟩
    · exact Or.inl ((hEd y).2 hy)
    rcases hm with hc | hd | ⟨-, hA, hB⟩
    · rcases (mem_marked_markedClosedSubset_univ_iff _ _ _ _).1 hc with hc | hc
      · exact Or.inl ((hEd _).2 ((isDegenerate_map_iso_iff e _).2 (isDegenerate_grayTensorCell
          (Or.inl (isDegenerate_app (closedSubpresheafUnivIso h.atom).inv hc)))))
      · exact Or.inr ((hT _).2 (Or.inl (Or.inl
          ((congrArg (fun z => z.1 ∈ h.targetMarking) (htopv e c d)).mpr hc))))
    · rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hd with hd | hd
      · exact Or.inl ((hEd _).2 ((isDegenerate_map_iso_iff e _).2
          (isDegenerate_grayTensorCell (Or.inr hd))))
      · exact Or.inr ((hT _).2 (Or.inl (Or.inr ((congrArg (fun z => marked = true ∧ z.2 = V.top)
          (htopv e c d)).mpr ((hMm _).1 hd)))))
    by_cases hcd : 0 < grade ℕ (ConcreteCategory.hom c.1.down A.top) ∧
        0 < grade ℕ (ConcreteCategory.hom d.down B.top)
    · exact Or.inr ((hT _).2 (Or.inr ((congrArg (fun z => 0 < grade ℕ z.1 ∧ 0 < grade ℕ z.2)
        (htopv e c d)).mpr hcd)))
    refine Or.inl ((hEd _).2 ((isDegenerate_map_iso_iff e _).2 (isDegenerate_grayTensorCell ?_)))
    rcases not_and_or.1 hcd with hc | hd
    · exact Or.inl (isDegenerate_app (closedSubpresheafUnivIso h.atom).inv
        (isDegenerate_ball_of_degenerate (degenerate_of_grade_lt (V := A) c.1.down (by omega))))
    · exact Or.inr (isDegenerate_ball_of_degenerate
        (degenerate_of_grade_lt (V := B) d.down (by omega)))
  rcases hy with hy | hy
  · exact Or.inl ((hEd y).1 hy)
  by_cases hdeg : IsDegenerate (grayTensor h.target.underlying (ball.{u} V)) y
  · exact Or.inl hdeg
  exact (mem_marked_markedTensor _ _ _ _ _).1
    (mem_marked_markedTensor_of_not_isDegenerate hU hV' hMm E hdeg hy)

variable {h V} in
private theorem exists_mem_marked_pt_of_mem_hornSet
    (f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM)
    {W A B : Atom} (c : diagram h.target.underlying A)
    (d : diagram (markedBall.{u} V M hM).underlying B) (e : W ≅ Atom.grayTensor A B)
    (hm : tensorMask true h.target (markedBall.{u} V M hM) A B c d)
    (hc : ConcreteCategory.hom c.1.down A.top ∈ h.hornSet) :
    ∃ x ∈ (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} true))
        (markedHornInclusion.{u} h) f₂).pt.marked W,
      (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h)
          f₂).ι).app (op W) x =
        (grayTensor h.target.underlying (markedBall.{u} V M hM).underlying).map e.hom.op
          (grayTensorCell c d) := by
  let c₀ : h.source.underlying.obj (op A) :=
    ⟨c.1, fun t => h.hornSet.lower ((Atom.isMap c.1.down).monotone (A.le_top t)) hc⟩
  have hy : (grayTensor _ _).map e.hom.op (grayTensorCell c₀ d) ∈
      (markedTensor true h.source (markedBall.{u} V M hM)).marked W :=
    (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨A, B, c₀, d, e,
      hm.imp_left (mem_marked_source_of_markedHornInclusion h c₀), rfl⟩)
  refine ⟨_, MarkedPresheaf.map_mem_marked (Functor.PushoutObjObj.ofHasPushout
    (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).inr hy,
      (congrFun (congrArg (fun φ => ((MarkedPresheaf.forget.map φ).app (op W) : _ → _))
        (Functor.PushoutObjObj.inr_ι _)) _).trans ?_⟩
  exact forget_map_markedTensorMap_app true (markedHornInclusion.{u} h) (𝟙 _) e.hom c₀ d

variable {h V marked} in
private theorem exists_mem_marked_pt_of_mem_bdryFull
    (hMm : ∀ b, b ∈ M ↔ marked = true ∧ b = V.top)
    {f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM}
    (hf₂ : MarkedPresheaf.forget.map f₂ = sphereInclusion V)
    {W A B : Atom} (c : diagram h.target.underlying A)
    (d : diagram (markedBall.{u} V M hM).underlying B) (e : W ≅ Atom.grayTensor A B)
    (hm : tensorMask true h.target (markedBall.{u} V M hM) A B c d)
    (hb : ConcreteCategory.hom d.down B.top ∈ V.ogp.bdryFull ⊤) :
    ∃ x ∈ (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} true))
        (markedHornInclusion.{u} h) f₂).pt.marked W,
      (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h)
          f₂).ι).app (op W) x =
        (grayTensor h.target.underlying (markedBall.{u} V M hM).underlying).map e.hom.op
          (grayTensorCell c d) := by
  have hd₀ : d ∈ (Homotopical.EZCategory.uliftBoundary.{u} V).obj (op B) := by
    rw [← closedSubpresheaf_univ_erase_top]
    exact fun t => (V.ogp.bdryFull ⊤).lower ((Atom.isMap d.down).monotone (B.le_top t)) hb
  let d₀ : (sphere.{u} V).obj (op B) := ⟨d, hd₀⟩
  have hm₀ : tensorMask true h.target ((MarkedPresheaf.flat atomMarking).obj (sphere.{u} V)) A B
      c d₀ := by
    rcases hm with hc | hd | hf
    · exact Or.inl hc
    · refine Or.inr (Or.inl ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ _ _).2 ?_))
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hd with hd | hd
      · exact isDegenerate_of_isDegenerate_app (sphereInclusion V) hd
      · exact absurd ((hMm _).1 hd).2 ((V.mem_bdryFull_top_iff _).1 hb)
    · exact Or.inr (Or.inr hf)
  have hy : (grayTensor _ _).map e.hom.op (grayTensorCell c d₀) ∈
      (markedTensor true h.target ((MarkedPresheaf.flat atomMarking).obj (sphere.{u} V))).marked
        W :=
    (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨A, B, c, d₀, e, hm₀, rfl⟩)
  refine ⟨_, MarkedPresheaf.map_mem_marked (Functor.PushoutObjObj.ofHasPushout
    (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).inl hy,
      (congrFun (congrArg (fun φ => ((MarkedPresheaf.forget.map φ).app (op W) : _ → _))
        (Functor.PushoutObjObj.inl_ι _)) _).trans ?_⟩
  refine (forget_map_markedTensorMap_app true (𝟙 _) f₂ e.hom c d₀).trans ?_
  rw [hf₂]
  rfl

variable {h V marked hV L R S hs hS ht} in
private theorem mem_marked_pt_of_mem_marked_ι (hMm : ∀ b, b ∈ M ↔ marked = true ∧ b = V.top)
    {f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM}
    (hf₂ : MarkedPresheaf.forget.map f₂ = sphereInclusion V)
    (E : Arrow.mk (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι) ≅
      Arrow.mk (MarkedPresheaf.forget.map (markedHornInclusion.{u}
        (h.pseudoGrayTensorRight V marked hV L R S hs hS ht))))
    {W : Atom} (x : (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h)
        f₂).pt.underlying.obj (op W))
    (hx : (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι).app
        (op W) x ∈ (markedTensor true h.target (markedBall.{u} V M hM)).marked W) :
    x ∈ (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} true))
      (markedHornInclusion.{u} h) f₂).pt.marked W := by
  have hmono : Mono (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι) :=
    ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff E).2 ((MarkedPresheaf.mono_iff _).1
      (markedHorns_le_monomorphisms _ (MorphismProperty.ofHoms.mk _)))
  have hinj := (mono_iff_injective ((MarkedPresheaf.forget.map
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} true))
      (markedHornInclusion.{u} h) f₂).ι).app (op W))).1 inferInstance
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hx with hd | ⟨A, B, c, d, e, hm, hx'⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _
      (@isDegenerate_of_isDegenerate_app _ _ _ hmono _ _ hd)
  have hw : E.hom.right.app (op W) ((MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι).app
        (op W) x) = (MarkedPresheaf.forget.map (markedHornInclusion.{u}
          (h.pseudoGrayTensorRight V marked hV L R S hs hS ht))).app (op W)
            (E.hom.left.app (op W) x) :=
    (congrFun (congrArg (fun φ => (NatTrans.app φ (op W) : _ → _)) E.hom.w) x).symm
  have h2 := (h.mem_hornSet_grayTensorRight_iff V (marked := marked) (hV := hV) (L := L) (R := R)
    (M := S) (hs := hs) (hM := hS) (ht := ht)).1
    ((congrArg (fun z : (closedSubpresheaf.{u} (Atom.grayTensor h.atom V) ⊤).toFunctor.obj (op W) =>
      ConcreteCategory.hom (z.1.down : W ⟶ _) W.top ∈
        (h.pseudoGrayTensorRight V marked hV L R S hs hS ht).hornSet) hw).mpr
      ((E.hom.left.app (op W) x).2 W.top))
  rw [hx'] at h2
  obtain ⟨x', hx'm, hx'x⟩ := ((congrArg (fun z => z.1 ∈ h.hornSet ∨ z.2 ∈ V.ogp.bdryFull ⊤)
    (grayTensorIso_inv_arrowIso_hom_right_app_top E e c d)).mp h2).elim
      (exists_mem_marked_pt_of_mem_hornSet f₂ c d e hm)
      (exists_mem_marked_pt_of_mem_bdryFull hMm hf₂ c d e hm)
  rwa [← hinj (hx'x.trans hx'.symm)]

private theorem nonempty_arrowIso_pseudoPushoutProduct (hU : 2 ≤ h.atom.dimension)
    (hV' : 0 < V.dimension) (hMm : ∀ b, b ∈ M ↔ marked = true ∧ b = V.top)
    (f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM)
    (hf₂ : MarkedPresheaf.forget.map f₂ = sphereInclusion V) :
    Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) f₂).ι ≅
      Arrow.mk (markedHornInclusion.{u} (h.pseudoGrayTensorRight V marked hV L R S hs hS ht))) := by
  obtain ⟨E⟩ := nonempty_forget_arrowIso true h
    (h.pseudoGrayTensorRight V marked hV L R S hs hS ht) V
    (h.toHornData_grayTensorRight V (marked := marked) (hV := hV) (L := L) (R := R) (M := S)
      (hs := hs) (hM := hS) (ht := ht)) f₂ hf₂
  refine nonempty_arrowIso_of_forget _ _ (fun _ x hx => ?_)
    (fun _ x hx => mem_marked_source_of_markedHornInclusion _ x hx) E
    (mem_marked_markedTensor_iff_arrowIso hU hV' hMm E)
  exact mem_marked_pt_of_mem_marked_ι hMm hf₂ E x hx

end HornSphere

theorem exists_arrowIso_pseudoPushoutProduct_markedHornInclusion_sphere (h : MarkedHornData)
    (V : Atom) (hU : 2 ≤ h.atom.dimension) (hV : 0 < V.dimension) :
    ∃ h' : MarkedHornData, h'.atom = Atom.grayTensor h.atom V ∧
      Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h)
        (sphereToMarkedBall V)).ι ≅ Arrow.mk (markedHornInclusion.{u} h')) := by
  obtain ⟨L, R, S, hs, hS, ht⟩ := h.exists_isStagedPasting_grayTensorRight V
  exact ⟨h.pseudoGrayTensorRight V false (fun h => absurd h Bool.false_ne_true) L R S hs hS ht, rfl,
    nonempty_arrowIso_pseudoPushoutProduct h V false _ L R S hs hS ht hU hV
      (fun b => ⟨fun hb => absurd hb (Set.notMem_empty b),
        fun hb => absurd hb.1 Bool.false_ne_true⟩)
      (sphereToMarkedBall V) rfl⟩

theorem exists_arrowIso_pseudoPushoutProduct_markedHornInclusion_markedSphere
    (h : MarkedHornData) (V : Atom) (hU : 2 ≤ h.atom.dimension) (hV : 0 < V.dimension) :
    ∃ h' : MarkedHornData, h'.atom = Atom.grayTensor h.atom V ∧
      Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h)
        (sphereToMarkedBall V ≫ markingToMarkedBall V hV)).ι ≅
          Arrow.mk (markedHornInclusion.{u} h')) := by
  obtain ⟨L, R, S, hs, hS, ht⟩ := h.exists_isStagedPasting_grayTensorRight V
  exact ⟨h.pseudoGrayTensorRight V true (fun _ => hV) L R S hs hS ht, rfl,
    nonempty_arrowIso_pseudoPushoutProduct h V true _ L R S hs hS ht hU hV
      (fun b => ⟨fun hb => ⟨rfl, hb⟩, fun hb => hb.2⟩) _
      ((Functor.map_comp _ _ _).trans (Category.comp_id (sphereInclusion V)))⟩

theorem MarkedDiagSet.Coinductive.weakEquivalence_pseudoPushoutProduct_markedHornInclusion_of_face
    (n : ℕ∞) (h : MarkedHornData) (hx : h.face ∈ h.targetMarking ∨ grade ℕ h.face = 0)
    {X Y : MarkedDiagSet.{u}} (i : X ⟶ Y) [Mono i] :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) (markedHornInclusion.{u} h) i).ι) := by
  have : Mono (markedHornInclusion.{u} h) := markedHorns_le_monomorphisms _ (.mk h)
  refine weakEquivalence_pseudoPushoutProduct_of_marked_left n _ i (fun W y hW hy => ?_)
    (weakEquivalence_pushoutProduct_markedHornInclusion n h i)
  refine (mem_marked_markedClosedSubset_univ_iff _ _ _ _).2 (or_iff_not_imp_left.2 fun hd => ?_)
  have hg : W.dimension ≤ grade ℕ (ConcreteCategory.hom y.1.down W.top) := not_lt.1 fun hlt =>
    hd (isDegenerate_ball_of_degenerate (degenerate_of_grade_lt _ hlt))
  have hh : ConcreteCategory.hom y.1.down W.top ∉ h.hornSet := fun hh =>
    hy ⟨⟨y.1, fun t => h.hornSet.lower ((Atom.isMap y.1.down).monotone (W.le_top t)) hh⟩, rfl⟩
  rw [h.mem_hornSet_iff, h.atom.mem_bdryFull_top_iff, not_and, not_not] at hh
  by_cases ht : ConcreteCategory.hom y.1.down W.top = h.atom.top
  · exact Or.inl ht
  rw [hh ht] at hg ⊢
  exact hx.resolve_right (by omega)

end Atoms.Diagrammatic
