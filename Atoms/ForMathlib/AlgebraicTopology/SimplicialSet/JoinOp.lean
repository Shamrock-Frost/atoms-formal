import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.JoinSlice

open CategoryTheory Limits Opposite Simplicial
open SimplexCategory (rev rev_map_apply)
open AugmentedSimplexCategory (tensorObjOf tensorHomOf inl' inr')

universe w w' u

namespace SSet

private lemma rev_map_inl'_comp_eqToHom (m n : SimplexCategory)
    (h : tensorObjOf m n = tensorObjOf n m) :
    rev.map (inl' m n) ≫ eqToHom h = inr' n m := by
  ext i
  have hi : (i : ℕ) < m.len + 1 := i.isLt
  simp [rev_map_apply, AugmentedSimplexCategory.inl'_eval, AugmentedSimplexCategory.inr'_eval]
  omega

private lemma rev_map_inr'_comp_eqToHom (m n : SimplexCategory)
    (h : tensorObjOf m n = tensorObjOf n m) :
    rev.map (inr' m n) ≫ eqToHom h = inl' n m := by
  ext i
  have hi : (i : ℕ) < n.len + 1 := i.isLt
  simp [rev_map_apply, AugmentedSimplexCategory.inl'_eval, AugmentedSimplexCategory.inr'_eval]
  omega

private lemma rev_map_tensorHomOf_comp_eqToHom {x₁ y₁ x₂ y₂ : SimplexCategory}
    (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) (h : tensorObjOf x₁ x₂ = tensorObjOf x₂ x₁)
    (h' : tensorObjOf y₁ y₂ = tensorObjOf y₂ y₁) :
    rev.map (tensorHomOf f g) ≫ eqToHom h' = eqToHom h ≫ tensorHomOf (rev.map g) (rev.map f) := by
  rw [← cancel_epi (eqToHom h.symm), eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  refine AugmentedSimplexCategory.tensorObj_hom_ext (x := .of x₂) (y := .of x₁)
    (z := .of (tensorObjOf y₂ y₁)) _ _ ?_ ?_
  · change inl' x₂ x₁ ≫ _ = inl' x₂ x₁ ≫ tensorHomOf _ _
    rw [AugmentedSimplexCategory.inl'_comp_tensorHomOf, ← rev_map_inr'_comp_eqToHom x₁ x₂ h,
      ← rev_map_inr'_comp_eqToHom y₁ y₂ h']
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Functor.map_comp_assoc, AugmentedSimplexCategory.inr'_comp_tensorHomOf]
  · change inr' x₂ x₁ ≫ _ = inr' x₂ x₁ ≫ tensorHomOf _ _
    rw [AugmentedSimplexCategory.inr'_comp_tensorHomOf, ← rev_map_inl'_comp_eqToHom x₁ x₂ h,
      ← rev_map_inl'_comp_eqToHom y₁ y₂ h']
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      ← Functor.map_comp_assoc, AugmentedSimplexCategory.inl'_comp_tensorHomOf]

@[reassoc]
private lemma opFunctor_map_stdSimplex_map_comp_opIso_hom {m n : SimplexCategory} (f : m ⟶ n) :
    opFunctor.map (stdSimplex.{u}.map f) ≫ (stdSimplex.opIso n).hom =
      (stdSimplex.opIso m).hom ≫ stdSimplex.map (rev.map f) := by
  ext ⟨k⟩ x
  induction k using SimplexCategory.rec with | _ d => ?_
  induction n using SimplexCategory.rec with | _ n => ?_
  refine stdSimplex.ext _ _ fun i ↦ ?_
  exact congrArg (fun j ↦ (f.toOrderHom j).rev) (Fin.rev_rev _).symm

@[reassoc]
private lemma stdSimplex_map_rev_map_comp_opIso_inv {m n : SimplexCategory} (f : m ⟶ n) :
    stdSimplex.{u}.map (rev.map f) ≫ (stdSimplex.opIso n).inv =
      (stdSimplex.opIso m).inv ≫ opFunctor.map (stdSimplex.map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, opFunctor_map_stdSimplex_map_comp_opIso_hom,
    Iso.inv_hom_id_assoc]

private lemma preservesColimitsOfSize_opFunctor :
    PreservesColimitsOfSize.{w, w'} opFunctor.{u} :=
  opEquivalence.toAdjunction.leftAdjoint_preservesColimits

private lemma preservesColimitsOfSize_under_post (T : SSet.{u}) :
    PreservesColimitsOfSize.{w, w'} (Under.post (X := T) opFunctor.{u}) :=
  (Under.postAdjunctionLeft opEquivalence.toAdjunction).leftAdjoint_preservesColimits

attribute [local instance] preservesColimitsOfSize_opFunctor preservesColimitsOfSize_under_post

private noncomputable def isoOfPreservesColimits {A : SSet.{u}}
    (F G : SSet.{u} ⥤ Under A) [PreservesColimitsOfSize.{0, u} F] [PreservesColimitsOfSize.{0, u} G]
    (e : uliftYoneda.{u} ⋙ F ≅ uliftYoneda.{u} ⋙ G) : F ≅ G :=
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} F (Iso.refl _)
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} G (Iso.refl _)
  Functor.leftKanExtensionUniqueOfIso F (Iso.refl _).hom e G (Iso.refl _).hom

private theorem isoOfPreservesColimits_hom_app {A : SSet.{u}}
    (F G : SSet.{u} ⥤ Under A) [PreservesColimitsOfSize.{0, u} F] [PreservesColimitsOfSize.{0, u} G]
    (e : uliftYoneda.{u} ⋙ F ≅ uliftYoneda.{u} ⋙ G) (n : SimplexCategory) :
    (isoOfPreservesColimits F G e).hom.app (uliftYoneda.obj n) = e.hom.app n := by
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} F (Iso.refl _)
  have h := F.descOfIsLeftKanExtension_fac_app (Iso.refl _).hom G (e.hom ≫ (Iso.refl _).hom) n
  refine Eq.trans ?_ (h.trans (by simp))
  simp [isoOfPreservesColimits]

private theorem ext_of_preservesColimits {F G : SSet.{u} ⥤ SSet.{u}}
    [PreservesColimitsOfSize.{0, u} F] {α β : ∀ K, F.obj K ⟶ G.obj K}
    (hα : ∀ {K K'} (f : K ⟶ K'), F.map f ≫ α K' = α K ≫ G.map f)
    (hβ : ∀ {K K'} (f : K ⟶ K'), F.map f ≫ β K' = β K ≫ G.map f)
    (h : ∀ n : ℕ, α Δ[n] = β Δ[n]) (K : SSet.{u}) : α K = β K := by
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} F (Iso.refl _)
  have key := F.hom_ext_of_isLeftKanExtension (Iso.refl (uliftYoneda.{u} ⋙ F)).hom
    (⟨α, fun _ _ f ↦ hα f⟩ : F ⟶ G) ⟨β, fun _ _ f ↦ hβ f⟩
    (NatTrans.ext (funext fun n ↦ by
      simp only [Iso.refl_hom, Functor.whiskerLeft_app, Category.id_comp]
      exact h n.len))
  exact congr_app key K

private theorem under_ext {A : SSet.{u}} (F : SSet.{u} ⥤ Under A)
    [PreservesColimitsOfSize.{0, u} F] {G : SSet.{u} ⥤ SSet.{u}}
    {α β : ∀ K, (F.obj K).right ⟶ G.obj K}
    (hα : ∀ {K K'} (f : K ⟶ K'), (F.map f).right ≫ α K' = α K ≫ G.map f)
    (hβ : ∀ {K K'} (f : K ⟶ K'), (F.map f).right ≫ β K' = β K ≫ G.map f)
    (hA : ∀ K, (F.obj K).hom ≫ α K = (F.obj K).hom ≫ β K)
    (h : ∀ n : ℕ, α Δ[n] = β Δ[n]) (K : SSet.{u}) : α K = β K := by
  let G' : SSet.{u} ⥤ Under A :=
    { obj K := Under.mk ((F.obj K).hom ≫ α K)
      map {K K'} f := Under.homMk (G.map f) ((Category.assoc _ _ _).trans
        ((congrArg _ (hα f).symm).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ α K') (Under.w (F.map f))))))
      map_id K := Under.UnderMorphism.ext (G.map_id K)
      map_comp f g := Under.UnderMorphism.ext (G.map_comp f g) }
  have := Presheaf.isLeftKanExtension_of_preservesColimits.{0, 0, u, 0, u + 1} F (Iso.refl _)
  have key := F.hom_ext_of_isLeftKanExtension (Iso.refl (uliftYoneda.{u} ⋙ F)).hom
    (⟨fun K ↦ Under.homMk (α K) rfl, fun _ _ f ↦ Under.UnderMorphism.ext (hα f)⟩ : F ⟶ G')
    ⟨fun K ↦ Under.homMk (β K) (hA K).symm, fun _ _ f ↦ Under.UnderMorphism.ext (hβ f)⟩
    (NatTrans.ext (funext fun n ↦ Under.UnderMorphism.ext (by
      simp only [Iso.refl_hom, Functor.whiskerLeft_app, Category.id_comp]
      exact h n.len)))
  exact congrArg CommaMorphism.right (congr_app key K)

private noncomputable def joinMapIso {X X' Y Y' : SSet.{u}} (e : X ≅ X') (e' : Y ≅ Y') :
    join X Y ≅ join X' Y' where
  hom := joinMap e.hom e'.hom
  inv := joinMap e.inv e'.inv
  hom_inv_id := by
    rw [joinMap_comp_joinMap, e.hom_inv_id, e'.hom_inv_id]
    exact joinFunctor.map_id (X, Y)
  inv_hom_id := by
    rw [joinMap_comp_joinMap, e.inv_hom_id, e'.inv_hom_id]
    exact joinFunctor.map_id (X', Y')

private lemma add_add_one_comm (m n : ℕ) : (⦋m + n + 1⦌ : SimplexCategory) = ⦋n + m + 1⦌ := by
  rw [Nat.add_comm m n]

private noncomputable def stdSimplexAddCommIso (m n : ℕ) :
    (Δ[m + n + 1] : SSet.{u}) ≅ Δ[n + m + 1] where
  hom := stdSimplex.map (eqToHom (add_add_one_comm m n))
  inv := stdSimplex.map (eqToHom (add_add_one_comm m n).symm)
  hom_inv_id := by
    rw [← stdSimplex.map_comp, eqToHom_trans, eqToHom_refl]
    exact stdSimplex.map_id _
  inv_hom_id := by
    rw [← stdSimplex.map_comp, eqToHom_trans, eqToHom_refl]
    exact stdSimplex.map_id _

private noncomputable def stdSimplexIso (m n : ℕ) :
    (join Δ[m] Δ[n]).op ≅ join (Δ[n] : SSet.{u}).op (Δ[m] : SSet.{u}).op :=
  opFunctor.mapIso (stdSimplexJoinIso m n) ≪≫ stdSimplex.opIso _ ≪≫
    stdSimplexAddCommIso m n ≪≫ (stdSimplexJoinIso n m).symm ≪≫
      joinMapIso (stdSimplex.opIso _).symm (stdSimplex.opIso _).symm

private lemma opFunctor_map_joinInclLeft_comp_stdSimplexIso_hom (m n : ℕ) :
    opFunctor.map (joinInclLeft Δ[m] Δ[n]) ≫ (stdSimplexIso.{u} m n).hom =
      joinInclRight _ _ := by
  have h : stdSimplex.map (inr' ⦋n⦌ ⦋m⦌) ≫ (stdSimplexJoinIso.{u} n m).inv =
      joinInclRight Δ[n] Δ[m] := by
    rw [Iso.comp_inv_eq, joinInclRight_comp_stdSimplexJoinIso_hom]
  simp only [stdSimplexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    stdSimplexAddCommIso]
  rw [← Functor.map_comp_assoc, joinInclLeft_comp_stdSimplexJoinIso_hom,
    opFunctor_map_stdSimplex_map_comp_opIso_hom_assoc, ← stdSimplex.map_comp_assoc,
    rev_map_inl'_comp_eqToHom, reassoc_of% h]
  exact (congrArg (_ ≫ ·) (joinInclRight_comp_joinMap _ _)).trans (Iso.hom_inv_id_assoc _ _)

private lemma opFunctor_map_joinInclRight_comp_stdSimplexIso_hom (m n : ℕ) :
    opFunctor.map (joinInclRight Δ[m] Δ[n]) ≫ (stdSimplexIso.{u} m n).hom =
      joinInclLeft _ _ := by
  have h : stdSimplex.map (inl' ⦋n⦌ ⦋m⦌) ≫ (stdSimplexJoinIso.{u} n m).inv =
      joinInclLeft Δ[n] Δ[m] := by
    rw [Iso.comp_inv_eq, joinInclLeft_comp_stdSimplexJoinIso_hom]
  simp only [stdSimplexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    stdSimplexAddCommIso]
  rw [← Functor.map_comp_assoc, joinInclRight_comp_stdSimplexJoinIso_hom,
    opFunctor_map_stdSimplex_map_comp_opIso_hom_assoc, ← stdSimplex.map_comp_assoc,
    rev_map_inr'_comp_eqToHom, reassoc_of% h]
  exact (congrArg (_ ≫ ·) (joinInclLeft_comp_joinMap _ _)).trans (Iso.hom_inv_id_assoc _ _)

private lemma stdSimplexIso_hom_naturality {k k' m m' : ℕ} (f : ⦋k⦌ ⟶ ⦋m⦌) (g : ⦋k'⦌ ⟶ ⦋m'⦌) :
    opFunctor.map (joinMap (stdSimplex.map f) (stdSimplex.map g)) ≫ (stdSimplexIso.{u} m m').hom =
      (stdSimplexIso k k').hom ≫
        joinMap (opFunctor.map (stdSimplex.map g)) (opFunctor.map (stdSimplex.map f)) := by
  have h : stdSimplex.map (tensorHomOf (rev.map g) (rev.map f)) ≫
      (stdSimplexJoinIso.{u} m' m).inv =
        (stdSimplexJoinIso k' k).inv ≫ joinMap (stdSimplex.map (rev.map g))
          (stdSimplex.map (rev.map f)) := by
    rw [Iso.comp_inv_eq, Category.assoc, joinMap_stdSimplex_map_comp_stdSimplexJoinIso_hom,
      Iso.inv_hom_id_assoc]
  simp only [stdSimplexIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    stdSimplexAddCommIso]
  rw [← Functor.map_comp_assoc, joinMap_stdSimplex_map_comp_stdSimplexJoinIso_hom,
    Functor.map_comp_assoc, opFunctor_map_stdSimplex_map_comp_opIso_hom_assoc,
    ← stdSimplex.map_comp_assoc, rev_map_tensorHomOf_comp_eqToHom _ _ (add_add_one_comm k k'),
    stdSimplex.map_comp_assoc, reassoc_of% h]
  simp only [joinMapIso, Iso.symm_hom, Category.assoc, joinMap_comp_joinMap,
    stdSimplex_map_rev_map_comp_opIso_inv]

private lemma preservesColimitsOfSize_shrink_joinLeftUnder (T : SSet.{u}) :
    PreservesColimitsOfSize.{0, u} (joinLeftUnder T) :=
  preservesColimitsOfSize_shrink _

private lemma preservesColimitsOfSize_shrink_joinRightUnder (T : SSet.{u}) :
    PreservesColimitsOfSize.{0, u} (joinRightUnder T) :=
  preservesColimitsOfSize_shrink _

attribute [local instance] preservesColimitsOfSize_shrink_joinLeftUnder
  preservesColimitsOfSize_shrink_joinRightUnder

private noncomputable def joinRightUnderStdSimplexIso (n : ℕ) :
    uliftYoneda.{u} ⋙ joinRightUnder Δ[n] ⋙ Under.post opFunctor ≅
      uliftYoneda.{u} ⋙ opFunctor ⋙ joinLeftUnder (Δ[n] : SSet.{u}).op :=
  NatIso.ofComponents (fun m ↦ Under.isoMk (stdSimplexIso m.len n)
      (opFunctor_map_joinInclRight_comp_stdSimplexIso_hom m.len n))
    (fun {m m'} g ↦ Under.UnderMorphism.ext (by
      have e : stdSimplex.map (𝟙 ⦋n⦌) = 𝟙 Δ[n] := stdSimplex.map_id _
      have e' : opFunctor.map (stdSimplex.map (𝟙 ⦋n⦌)) = 𝟙 (Δ[n] : SSet.{u}).op :=
        (congrArg opFunctor.map e).trans (opFunctor.map_id _)
      exact (congrArg (fun x ↦ opFunctor.map (joinMap (stdSimplex.map g) x) ≫
        (stdSimplexIso m'.len n).hom) e).symm.trans
          ((stdSimplexIso_hom_naturality.{u} (k := m.len) (m := m'.len) g (𝟙 ⦋n⦌)).trans
            (congrArg (fun x ↦ (stdSimplexIso m.len n).hom ≫
              joinMap x (opFunctor.map (stdSimplex.map g))) e'))))

private noncomputable def joinRightUnderStdSimplexOpIso (n : ℕ) :
    joinRightUnder Δ[n] ⋙ Under.post opFunctor ≅
      opFunctor ⋙ joinLeftUnder (Δ[n] : SSet.{u}).op :=
  isoOfPreservesColimits _ _ (joinRightUnderStdSimplexIso n)

private noncomputable def joinStdSimplexOpIso (K : SSet.{u}) (n : ℕ) :
    (join K Δ[n]).op ≅ join (Δ[n] : SSet.{u}).op K.op :=
  (Under.forget _).mapIso ((joinRightUnderStdSimplexOpIso n).app K)

private lemma opFunctor_map_joinInclRight_comp_joinStdSimplexOpIso_hom (K : SSet.{u}) (n : ℕ) :
    opFunctor.map (joinInclRight K Δ[n]) ≫ (joinStdSimplexOpIso K n).hom =
      joinInclLeft _ _ :=
  Under.w ((joinRightUnderStdSimplexOpIso n).hom.app K)

private lemma joinStdSimplexOpIso_hom_naturality {K K' : SSet.{u}} (f : K ⟶ K') (n : ℕ) :
    opFunctor.map (joinMap f (𝟙 Δ[n])) ≫ (joinStdSimplexOpIso K' n).hom =
      (joinStdSimplexOpIso K n).hom ≫ joinMap (𝟙 _) (opFunctor.map f) :=
  congrArg CommaMorphism.right ((joinRightUnderStdSimplexOpIso n).hom.naturality f)

private lemma joinStdSimplexOpIso_stdSimplex (m n : ℕ) :
    (joinStdSimplexOpIso Δ[m] n).hom = (stdSimplexIso.{u} m n).hom :=
  congrArg CommaMorphism.right
    (isoOfPreservesColimits_hom_app _ _ (joinRightUnderStdSimplexIso n) ⦋m⦌)

private lemma opFunctor_map_joinInclLeft_comp_joinStdSimplexOpIso_hom (K : SSet.{u}) (n : ℕ) :
    opFunctor.map (joinInclLeft K Δ[n]) ≫ (joinStdSimplexOpIso K n).hom =
      joinInclRight _ _ :=
  ext_of_preservesColimits (F := opFunctor)
    (G := opFunctor ⋙ joinLeftUnder (Δ[n] : SSet.{u}).op ⋙ Under.forget _)
    (α := fun K ↦ opFunctor.map (joinInclLeft K Δ[n]) ≫ (joinStdSimplexOpIso K n).hom)
    (β := fun K ↦ joinInclRight _ K.op)
    (fun f ↦ (Functor.map_comp_assoc _ _ _ _).symm.trans
      ((congrArg (fun x ↦ opFunctor.map x ≫ _) (joinInclLeft_comp_joinMap f (𝟙 Δ[n])).symm).trans
        ((Functor.map_comp_assoc _ _ _ _).trans
          ((congrArg (_ ≫ ·) (joinStdSimplexOpIso_hom_naturality f n)).trans
            (Category.assoc _ _ _).symm))))
    (fun _ ↦ (joinInclRight_comp_joinMap _ _).symm)
    (fun m ↦ (congrArg (_ ≫ ·) (joinStdSimplexOpIso_stdSimplex m n)).trans
      (opFunctor_map_joinInclLeft_comp_stdSimplexIso_hom m n)) K

private lemma joinMap_id_comp_joinMap_id {X X' Y Y' : SSet.{u}} (f : X ⟶ X') (g : Y ⟶ Y') :
    joinMap f (𝟙 Y) ≫ joinMap (𝟙 X') g = joinMap (𝟙 X) g ≫ joinMap f (𝟙 Y') := by
  rw [joinMap_comp_joinMap, joinMap_comp_joinMap, Category.comp_id, Category.id_comp,
    Category.id_comp, Category.comp_id]

private lemma joinStdSimplexOpIso_hom_naturality_right (K : SSet.{u}) {n n' : ℕ}
    (g : ⦋n⦌ ⟶ ⦋n'⦌) :
    opFunctor.map (joinMap (𝟙 K) (stdSimplex.map g)) ≫ (joinStdSimplexOpIso K n').hom =
      (joinStdSimplexOpIso K n).hom ≫ joinMap (opFunctor.map (stdSimplex.map g)) (𝟙 _) :=
  under_ext (joinRightUnder Δ[n] ⋙ Under.post opFunctor)
    (G := opFunctor ⋙ joinLeftUnder (Δ[n'] : SSet.{u}).op ⋙ Under.forget _)
    (α := fun K ↦ opFunctor.map (joinMap (𝟙 K) (stdSimplex.map g)) ≫
      (joinStdSimplexOpIso K n').hom)
    (β := fun K ↦ (joinStdSimplexOpIso K n).hom ≫
      joinMap (opFunctor.map (stdSimplex.map g)) (𝟙 _))
    (fun f ↦ (Functor.map_comp_assoc _ _ _ _).symm.trans
      ((congrArg (fun x ↦ opFunctor.map x ≫ _) (joinMap_id_comp_joinMap_id f _)).trans
        ((Functor.map_comp_assoc _ _ _ _).trans
          ((congrArg (_ ≫ ·) (joinStdSimplexOpIso_hom_naturality f n')).trans
            (Category.assoc _ _ _).symm))))
    (fun f ↦ (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (joinStdSimplexOpIso_hom_naturality f n)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (joinMap_id_comp_joinMap_id _ _).symm).trans
            (Category.assoc _ _ _).symm))))
    (fun K ↦ by
      have h : opFunctor.map (joinInclRight K Δ[n]) ≫
          opFunctor.map (joinMap (𝟙 K) (stdSimplex.map g)) ≫ (joinStdSimplexOpIso K n').hom =
            opFunctor.map (stdSimplex.map g) ≫ joinInclLeft _ K.op :=
        (Functor.map_comp_assoc _ _ _ _).symm.trans
          ((congrArg (fun x ↦ opFunctor.map x ≫ _) (joinInclRight_comp_joinMap _ _)).trans
            ((Functor.map_comp_assoc _ _ _ _).trans (congrArg (_ ≫ ·)
              (opFunctor_map_joinInclRight_comp_joinStdSimplexOpIso_hom K n'))))
      have h' : opFunctor.map (joinInclRight K Δ[n]) ≫ (joinStdSimplexOpIso K n).hom ≫
          joinMap (opFunctor.map (stdSimplex.map g)) (𝟙 K.op) =
            opFunctor.map (stdSimplex.map g) ≫ joinInclLeft _ K.op :=
        (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ _) (opFunctor_map_joinInclRight_comp_joinStdSimplexOpIso_hom K n)).trans
            (joinInclLeft_comp_joinMap _ _))
      exact h.trans h'.symm)
    (fun m ↦ by
      have e : stdSimplex.map (𝟙 ⦋m⦌) = 𝟙 Δ[m] := stdSimplex.map_id _
      have e' : opFunctor.map (stdSimplex.map (𝟙 ⦋m⦌)) = 𝟙 (Δ[m] : SSet.{u}).op :=
        (congrArg opFunctor.map e).trans (opFunctor.map_id _)
      refine (congrArg (_ ≫ ·) (joinStdSimplexOpIso_stdSimplex m n')).trans
        (Eq.trans ?_ (congrArg (· ≫ _) (joinStdSimplexOpIso_stdSimplex m n).symm))
      exact (congrArg (fun x ↦ opFunctor.map (joinMap x (stdSimplex.map g)) ≫
        (stdSimplexIso m n').hom) e).symm.trans
          ((stdSimplexIso_hom_naturality.{u} (𝟙 ⦋m⦌) g).trans
            (congrArg (fun x ↦ (stdSimplexIso m n).hom ≫
              joinMap (opFunctor.map (stdSimplex.map g)) x) e'))) K

private noncomputable def joinLeftUnderStdSimplexIso (K : SSet.{u}) :
    uliftYoneda.{u} ⋙ joinLeftUnder K ⋙ Under.post opFunctor ≅
      uliftYoneda.{u} ⋙ opFunctor ⋙ joinRightUnder K.op :=
  NatIso.ofComponents (fun n ↦ Under.isoMk (joinStdSimplexOpIso K n.len)
      (opFunctor_map_joinInclLeft_comp_joinStdSimplexOpIso_hom K n.len))
    (fun {n n'} g ↦ Under.UnderMorphism.ext
      (joinStdSimplexOpIso_hom_naturality_right K (n := n.len) (n' := n'.len) g))

noncomputable def joinLeftUnderOpIso (K : SSet.{u}) :
    joinLeftUnder K ⋙ Under.post opFunctor ≅ opFunctor ⋙ joinRightUnder K.op :=
  isoOfPreservesColimits _ _ (joinLeftUnderStdSimplexIso K)

noncomputable def joinOpIso (K L : SSet.{u}) : (join K L).op ≅ join L.op K.op :=
  (Under.forget _).mapIso ((joinLeftUnderOpIso K).app L)

@[reassoc]
theorem opFunctor_map_joinInclLeft_comp_joinOpIso_hom (K L : SSet.{u}) :
    opFunctor.map (joinInclLeft K L) ≫ (joinOpIso K L).hom = joinInclRight L.op K.op :=
  Under.w ((joinLeftUnderOpIso K).hom.app L)

private lemma joinOpIso_stdSimplex (K : SSet.{u}) (n : ℕ) :
    (joinOpIso K Δ[n]).hom = (joinStdSimplexOpIso K n).hom :=
  congrArg CommaMorphism.right
    (isoOfPreservesColimits_hom_app _ _ (joinLeftUnderStdSimplexIso K) ⦋n⦌)

@[reassoc]
private lemma joinOpIso_hom_naturality_right (K : SSet.{u}) {L L' : SSet.{u}} (g : L ⟶ L') :
    opFunctor.map (joinMap (𝟙 K) g) ≫ (joinOpIso K L').hom =
      (joinOpIso K L).hom ≫ joinMap (opFunctor.map g) (𝟙 K.op) :=
  congrArg CommaMorphism.right ((joinLeftUnderOpIso K).hom.naturality g)

private lemma joinOpIso_hom_naturality_left {K K' : SSet.{u}} (f : K ⟶ K') (L : SSet.{u}) :
    opFunctor.map (joinMap f (𝟙 L)) ≫ (joinOpIso K' L).hom =
      (joinOpIso K L).hom ≫ joinMap (𝟙 L.op) (opFunctor.map f) :=
  under_ext (joinLeftUnder K ⋙ Under.post opFunctor)
    (G := opFunctor ⋙ joinRightUnder K'.op ⋙ Under.forget _)
    (α := fun L ↦ opFunctor.map (joinMap f (𝟙 L)) ≫ (joinOpIso K' L).hom)
    (β := fun L ↦ (joinOpIso K L).hom ≫ joinMap (𝟙 L.op) (opFunctor.map f))
    (fun g ↦ (Functor.map_comp_assoc _ _ _ _).symm.trans
      ((congrArg (fun x ↦ opFunctor.map x ≫ _) (joinMap_id_comp_joinMap_id f g).symm).trans
        ((Functor.map_comp_assoc _ _ _ _).trans
          ((congrArg (_ ≫ ·) (joinOpIso_hom_naturality_right K' g)).trans
            (Category.assoc _ _ _).symm))))
    (fun g ↦ (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (joinOpIso_hom_naturality_right K g)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) (joinMap_id_comp_joinMap_id _ _)).trans
            (Category.assoc _ _ _).symm))))
    (fun L ↦ by
      have h : opFunctor.map (joinInclLeft K L) ≫ opFunctor.map (joinMap f (𝟙 L)) ≫
          (joinOpIso K' L).hom = opFunctor.map f ≫ joinInclRight L.op K'.op := by
        rw [← Functor.map_comp_assoc, joinInclLeft_comp_joinMap, Functor.map_comp_assoc,
          opFunctor_map_joinInclLeft_comp_joinOpIso_hom]
      have h' : opFunctor.map (joinInclLeft K L) ≫ (joinOpIso K L).hom ≫
          joinMap (𝟙 L.op) (opFunctor.map f) = opFunctor.map f ≫ joinInclRight L.op K'.op := by
        rw [opFunctor_map_joinInclLeft_comp_joinOpIso_hom_assoc, joinInclRight_comp_joinMap]
      exact h.trans h'.symm)
    (fun n ↦ (congrArg (_ ≫ ·) (joinOpIso_stdSimplex K' n)).trans
      ((joinStdSimplexOpIso_hom_naturality f n).trans
        (congrArg (· ≫ _) (joinOpIso_stdSimplex K n).symm))) L

@[reassoc]
theorem opFunctor_map_joinInclRight_comp_joinOpIso_hom (K L : SSet.{u}) :
    opFunctor.map (joinInclRight K L) ≫ (joinOpIso K L).hom = joinInclLeft L.op K.op :=
  ext_of_preservesColimits (F := opFunctor)
    (G := opFunctor ⋙ joinRightUnder K.op ⋙ Under.forget _)
    (α := fun L ↦ opFunctor.map (joinInclRight K L) ≫ (joinOpIso K L).hom)
    (β := fun L ↦ joinInclLeft L.op K.op)
    (fun g ↦ (Functor.map_comp_assoc _ _ _ _).symm.trans
      ((congrArg (fun x ↦ opFunctor.map x ≫ _) (joinInclRight_comp_joinMap (𝟙 K) g).symm).trans
        ((Functor.map_comp_assoc _ _ _ _).trans
          ((congrArg (_ ≫ ·) (joinOpIso_hom_naturality_right K g)).trans
            (Category.assoc _ _ _).symm))))
    (fun _ ↦ (joinInclLeft_comp_joinMap _ _).symm)
    (fun n ↦ (congrArg (_ ≫ ·) (joinOpIso_stdSimplex K n)).trans
      (opFunctor_map_joinInclRight_comp_joinStdSimplexOpIso_hom K n)) L

@[reassoc]
theorem joinOpIso_hom_naturality {K K' L L' : SSet.{u}} (f : K ⟶ K') (g : L ⟶ L') :
    opFunctor.map (joinMap f g) ≫ (joinOpIso K' L').hom =
      (joinOpIso K L).hom ≫ joinMap (opFunctor.map g) (opFunctor.map f) := by
  have hfg : joinMap f g = joinMap f (𝟙 L) ≫ joinMap (𝟙 K') g := by
    rw [joinMap_comp_joinMap, Category.comp_id, Category.id_comp]
  have hgf : joinMap (opFunctor.map g) (opFunctor.map f) =
      joinMap (𝟙 L.op) (opFunctor.map f) ≫ joinMap (opFunctor.map g) (𝟙 K'.op) := by
    rw [joinMap_comp_joinMap, Category.comp_id, Category.id_comp]
  rw [hfg, Functor.map_comp_assoc, joinOpIso_hom_naturality_right,
    reassoc_of% joinOpIso_hom_naturality_left, hgf]

noncomputable def joinRightUnderOpIso (L : SSet.{u}) :
    joinRightUnder L ⋙ Under.post opFunctor ≅ opFunctor ⋙ joinLeftUnder L.op :=
  NatIso.ofComponents (fun K ↦ Under.isoMk (joinOpIso K L)
      (opFunctor_map_joinInclRight_comp_joinOpIso_hom K L))
    (fun f ↦ Under.UnderMorphism.ext (joinOpIso_hom_naturality_left f L))

private noncomputable def stdSimplexOpNatIso :
    rev ⋙ uliftYoneda.{u} ⋙ opFunctor ≅ uliftYoneda.{u} :=
  NatIso.ofComponents (fun n ↦ stdSimplex.opIso n) (fun f ↦
    (opFunctor_map_stdSimplex_map_comp_opIso_hom (rev.map f)).trans
      (congrArg (_ ≫ stdSimplex.map ·) (SimplexCategory.rev_map_rev_map f)))

private noncomputable def restrictedULiftYonedaOpIso {E E' : Type (u + 1)} [Category.{u} E]
    [Category.{u} E'] {P : E ⥤ E'} (hP : P.FullyFaithful) {F : SimplexCategory ⥤ E}
    {G : SimplexCategory ⥤ E'} (φ : G ≅ rev ⋙ F ⋙ P) :
    Presheaf.restrictedULiftYoneda.{0} F ⋙ opFunctor ≅
      P ⋙ Presheaf.restrictedULiftYoneda.{0} G :=
  NatIso.ofComponents (fun t ↦ NatIso.ofComponents (fun n ↦ Equiv.toIso
    { toFun x := ULift.up (φ.hom.app n.unop ≫ P.map x.down)
      invFun y := ULift.up (hP.preimage (φ.inv.app n.unop ≫ y.down))
      left_inv x := ULift.ext _ _ (by
        simp only [Iso.inv_hom_id_app_assoc, Functor.FullyFaithful.preimage_map])
      right_inv y := ULift.ext _ _ (by
        simp only [Functor.FullyFaithful.map_preimage, Iso.hom_inv_id_app_assoc]) })
    (fun {n n'} θ ↦ by
      ext ⟨x⟩
      exact ULift.ext _ _ ((congrArg (φ.hom.app _ ≫ ·) (P.map_comp _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ P.map x)
          (φ.hom.naturality θ.unop).symm).trans (Category.assoc _ _ _))))))
    (fun g ↦ by
      ext n ⟨x⟩
      exact ULift.ext _ _ ((congrArg (_ ≫ ·) (P.map_comp _ _)).trans
        (Category.assoc _ _ _).symm))

noncomputable def cosliceOpIso (K : SSet.{u}) :
    coslice K ⋙ opFunctor ≅ Under.post opFunctor ⋙ slice K.op :=
  restrictedULiftYonedaOpIso (P := Under.post opFunctor)
    (opEquivalence.fullyFaithfulFunctor.under (X := K))
    (Functor.isoWhiskerRight stdSimplexOpNatIso.symm (joinRightUnder K.op) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft rev (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft uliftYoneda (joinLeftUnderOpIso K).symm ≪≫
          (Functor.associator _ _ _).symm))

noncomputable def sliceOpIso (K : SSet.{u}) :
    slice K ⋙ opFunctor ≅ Under.post opFunctor ⋙ coslice K.op :=
  restrictedULiftYonedaOpIso (P := Under.post opFunctor)
    (opEquivalence.fullyFaithfulFunctor.under (X := K))
    (Functor.isoWhiskerRight stdSimplexOpNatIso.symm (joinLeftUnder K.op) ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft rev (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft uliftYoneda (joinRightUnderOpIso K).symm ≪≫
          (Functor.associator _ _ _).symm))

theorem sliceObjEquiv_cosliceOpIso_hom_app_app_coe {K : SSet.{u}} (t : Under K) (n : ℕ)
    (σ : ((coslice K).obj t) _⦋n⦌) :
    (sliceObjEquiv K.op ((Under.post opFunctor).obj t) n
      (((cosliceOpIso K).hom.app t).app _ (opObjEquiv.symm σ))).1 =
        joinMap (stdSimplex.opIso ⦋n⦌).inv (𝟙 K.op) ≫ (joinOpIso K Δ[n]).inv ≫
          opFunctor.map (cosliceObjEquiv K t n σ).1 :=
  rfl

theorem cosliceObjEquiv_sliceOpIso_hom_app_app_coe {K : SSet.{u}} (t : Under K) (n : ℕ)
    (σ : ((slice K).obj t) _⦋n⦌) :
    (cosliceObjEquiv K.op ((Under.post opFunctor).obj t) n
      (((sliceOpIso K).hom.app t).app _ (opObjEquiv.symm σ))).1 =
        joinMap (𝟙 K.op) (stdSimplex.opIso ⦋n⦌).inv ≫ (joinOpIso Δ[n] K).inv ≫
          opFunctor.map (sliceObjEquiv K t n σ).1 :=
  rfl

end SSet
