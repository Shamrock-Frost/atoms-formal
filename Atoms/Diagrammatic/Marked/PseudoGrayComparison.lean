import Atoms.Diagrammatic.Marked.FlatEquivalence
import Atoms.Diagrammatic.Marked.GrayTensorMonoidal
import Atoms.ForMathlib.CategoryTheory.Adjunction.Mates

open CategoryTheory Limits HomotopicalAlgebra Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem MarkedDiagSet.Coinductive.weakEquivalence_of_isIso_forget_map_of_lt (n : ℕ∞)
    {A B : MarkedDiagSet.{u}} (i : A ⟶ B) [IsIso (MarkedPresheaf.forget.map i)]
    (h : ∀ (U : Atom) (x : diagram B.underlying U), x ∈ B.marked U →
      (∃ y : diagram A.underlying U, y ∈ A.marked U ∧
        (MarkedPresheaf.forget.map i).app _ y = x) ∨ n < U.dimension) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map i) := by
  refine weakEquivalence_of_isIso_forget_map n i fun Z hZ g hg U x hx => ?_
  rcases h U x hx with ⟨y, hy, rfl⟩ | hd
  · exact hg U y hy
  · exact hZ.2 U (g.app _ x) hd

theorem bijective_comp_of_isIso_forget_map {m : ℕ} {A B Z : MarkedDiagSet.{u}} (i : A ⟶ B)
    [IsIso (MarkedPresheaf.forget.map i)]
    (h : ∀ (U : Atom) (x : diagram B.underlying U), x ∈ B.marked U →
      (∃ y : diagram A.underlying U, y ∈ A.marked U ∧
        (MarkedPresheaf.forget.map i).app _ y = x) ∨ m < U.dimension)
    (hZ : ∀ (U : Atom) (z : diagram Z.underlying U), m < U.dimension → z ∈ Z.marked U) :
    Function.Bijective fun g : B ⟶ Z => i ≫ g := by
  refine ⟨fun g₁ g₂ hg => MarkedPresheaf.hom_ext ?_, fun g => ?_⟩
  · rw [← cancel_epi (MarkedPresheaf.forget.map i), ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg MarkedPresheaf.forget.map hg
  · let l := inv (MarkedPresheaf.forget.map i) ≫ MarkedPresheaf.forget.map g
    have hl : MarkedPresheaf.forget.map i ≫ l = MarkedPresheaf.forget.map g :=
      IsIso.hom_inv_id_assoc _ _
    refine ⟨MarkedPresheaf.homMk l fun U x hx => ?_, MarkedPresheaf.hom_ext ?_⟩
    · rcases h U x hx with ⟨y, hy, rfl⟩ | hd
      · have e : l.app _ ((MarkedPresheaf.forget.map i).app _ y) =
            (MarkedPresheaf.forget.map g).app _ y :=
          ConcreteCategory.congr_hom (congr_app hl _) y
        exact e ▸ MarkedPresheaf.map_mem_marked g hy
      · exact hZ U _ hd
    · exact (Functor.map_comp _ _ _).trans hl

private theorem mem_marked_markedTensor_false_or_one_lt {X Y : MarkedDiagSet.{u}} {T : Atom}
    {z : diagram (grayTensor X.underlying Y.underlying) T}
    (hz : z ∈ (markedTensor true X Y).marked T) :
    z ∈ (markedTensor false X Y).marked T ∨ 1 < T.dimension := by
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hz with hz | ⟨U, V, x, y, e, hm, rfl⟩
  · exact Or.inl ((mem_marked_markedTensor _ _ _ _ _).2 (Or.inl hz))
  · by_cases hd : 1 < T.dimension
    · exact Or.inr hd
    · refine Or.inl ((mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨U, V, x, y, e, ?_, rfl⟩))
      refine hm.imp_right (Or.imp_right fun ⟨_, hU, hV⟩ => absurd ?_ hd)
      rw [Atom.dimension_eq_of_iso e, Atom.dimension_grayTensor]
      omega

private theorem grayToPseudo_marked (X Y : MarkedDiagSet.{u}) (U : Atom)
    (x : diagram (markedTensor true X Y).underlying U) (hx : x ∈ (markedTensor true X Y).marked U) :
    (∃ y : diagram (markedTensor false X Y).underlying U, y ∈ (markedTensor false X Y).marked U ∧
      (MarkedPresheaf.forget.map (grayToPseudo X Y)).app _ y = x) ∨ 1 < U.dimension :=
  (mem_marked_markedTensor_false_or_one_lt hx).imp_left fun h => ⟨x, h, rfl⟩

private theorem lt_of_one_lt {n : ℕ∞} (hn : n ≤ 1) {d : ℕ} (h : 1 < d) : n < d :=
  hn.trans_lt (by exact_mod_cast h)

theorem MarkedDiagSet.Coinductive.weakEquivalence_grayToPseudo (n : ℕ∞) (hn : n ≤ 1)
    (X Y : MarkedDiagSet.{u}) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (grayToPseudo X Y)) :=
  weakEquivalence_of_isIso_forget_map_of_lt n _ fun U x hx =>
    (grayToPseudo_marked X Y U x hx).imp_right (lt_of_one_lt hn)

theorem MarkedDiagSet.Coinductive.mem_marked_of_isFibrant (n : ℕ∞) (hn : n ≤ 1)
    {Z : MarkedDiagSet.{u}} (hZ : IsFibrant ((MarkedDiagSet.toCoinductive n).obj Z))
    (U : Atom) (z : diagram Z.underlying U) (hU : 1 < U.dimension) : z ∈ Z.marked U :=
  have h := (isFibrant_coinductive_iff_natural n _).1 hZ
  (h.2 U z).2 (h.1.2 U z (lt_of_one_lt hn hU))

noncomputable def grayToPseudoRight (X : MarkedDiagSet.{u}) :
    tensorRight false X ⟶ tensorRight true X where
  app T := grayToPseudo T X
  naturality _ _ f := grayToPseudo_naturality f (𝟙 X)

@[simp] theorem grayToPseudoRight_app (X T : MarkedDiagSet.{u}) :
    (grayToPseudoRight X).app T = grayToPseudo T X :=
  rfl

noncomputable def grayToPseudoLeft (X : MarkedDiagSet.{u}) :
    tensorLeft false X ⟶ tensorLeft true X where
  app T := grayToPseudo X T
  naturality _ _ f := grayToPseudo_naturality (𝟙 X) f

@[simp] theorem grayToPseudoLeft_app (X T : MarkedDiagSet.{u}) :
    (grayToPseudoLeft X).app T = grayToPseudo X T :=
  rfl

private theorem grayToPseudoLeft_naturality_left {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y)
    (T : MarkedDiagSet.{u}) :
    ((Functor.curry.obj (markedTensorBifunctor.{u} false)).map f).app T ≫
        (grayToPseudoLeft Y).app T =
      (grayToPseudoLeft X).app T ≫
        ((Functor.curry.obj (markedTensorBifunctor.{u} true)).map f).app T :=
  grayToPseudo_naturality f (𝟙 T)

section PushoutProduct

variable {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

noncomputable def pushoutObjGrayToPseudo :
    (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).pt ⟶
    (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).pt :=
  (Functor.PushoutObjObj.ofHasPushout _ f₁ f₂).isPushout.desc
    ((grayToPseudoLeft Y₁).app X₂ ≫ (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).inl)
    ((grayToPseudoLeft X₁).app Y₂ ≫ (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).inr)
    (by rw [reassoc_of% grayToPseudoLeft_naturality_left, NatTrans.naturality_assoc,
      (Functor.PushoutObjObj.ofHasPushout _ f₁ f₂).isPushout.w])

theorem inl_pushoutObjGrayToPseudo :
    (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).inl ≫
        pushoutObjGrayToPseudo f₁ f₂ =
      (grayToPseudoLeft Y₁).app X₂ ≫ (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).inl :=
  IsPushout.inl_desc _ _ _ _

theorem inr_pushoutObjGrayToPseudo :
    (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).inr ≫
        pushoutObjGrayToPseudo f₁ f₂ =
      (grayToPseudoLeft X₁).app Y₂ ≫ (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).inr :=
  IsPushout.inr_desc _ _ _ _

theorem pushoutProduct_comp_grayToPseudo :
    (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι ≫
        (grayToPseudoLeft Y₁).app Y₂ =
    pushoutObjGrayToPseudo f₁ f₂ ≫ (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).ι := by
  refine (Functor.PushoutObjObj.ofHasPushout _ f₁ f₂).isPushout.hom_ext ?_ ?_
  · rw [Functor.PushoutObjObj.inl_ι_assoc, reassoc_of% inl_pushoutObjGrayToPseudo,
      Functor.PushoutObjObj.inl_ι, NatTrans.naturality]
  · rw [Functor.PushoutObjObj.inr_ι_assoc, reassoc_of% inr_pushoutObjGrayToPseudo,
      Functor.PushoutObjObj.inr_ι, grayToPseudoLeft_naturality_left]

instance isIso_forget_map_pushoutObjGrayToPseudo :
    IsIso (MarkedPresheaf.forget.map (pushoutObjGrayToPseudo f₁ f₂)) := by
  let F₀ := Functor.curry.obj (markedTensorBifunctor.{u} false)
  let F₁ := Functor.curry.obj (markedTensorBifunctor.{u} true)
  have h₀ := (Functor.PushoutObjObj.ofHasPushout F₀ f₁ f₂).isPushout.map MarkedPresheaf.forget
  have h₁ := (Functor.PushoutObjObj.ofHasPushout F₁ f₁ f₂).isPushout.map MarkedPresheaf.forget
  have : MarkedPresheaf.forget.map (pushoutObjGrayToPseudo f₁ f₂) =
      (h₀.isoIsPushout _ _ h₁).hom := by
    refine h₀.hom_ext ?_ ?_
    · exact ((Functor.map_comp _ _ _).symm.trans
        ((congrArg _ (inl_pushoutObjGrayToPseudo f₁ f₂)).trans
        ((Functor.map_comp _ _ _).trans (Category.id_comp _)))).trans
        (IsPushout.inl_isoIsPushout_hom _ _ h₀ h₁).symm
    · exact ((Functor.map_comp _ _ _).symm.trans
        ((congrArg _ (inr_pushoutObjGrayToPseudo f₁ f₂)).trans
        ((Functor.map_comp _ _ _).trans (Category.id_comp _)))).trans
        (IsPushout.inr_isoIsPushout_hom _ _ h₀ h₁).symm
  rw [this]
  infer_instance

private theorem exists_mem_marked_of_comp_eq {X Y P₀ P₁ : MarkedDiagSet.{u}}
    (ℓ₀ : markedTensor false X Y ⟶ P₀) (ℓ₁ : markedTensor true X Y ⟶ P₁) (φ : P₀ ⟶ P₁)
    (hφ : ℓ₀ ≫ φ = grayToPseudo X Y ≫ ℓ₁) {U : Atom}
    {x : diagram (markedTensor true X Y).underlying U}
    (hx : x ∈ (markedTensor true X Y).marked U) :
    (∃ y : diagram P₀.underlying U, y ∈ P₀.marked U ∧
      (MarkedPresheaf.forget.map φ).app _ y = (MarkedPresheaf.forget.map ℓ₁).app _ x) ∨
      1 < U.dimension := by
  refine (mem_marked_markedTensor_false_or_one_lt hx).imp_left fun h =>
    ⟨_, MarkedPresheaf.map_mem_marked ℓ₀ h, ?_⟩
  have e := congrArg MarkedPresheaf.forget.map hφ
  rw [Functor.map_comp, Functor.map_comp] at e
  exact ConcreteCategory.congr_hom (congr_app e _) x

private theorem pushoutObjGrayToPseudo_marked (U : Atom)
    (x : diagram (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).pt.underlying U)
    (hx : x ∈ (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).pt.marked U) :
    (∃ y : diagram (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).pt.underlying U,
      y ∈ (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).pt.marked U ∧
      (MarkedPresheaf.forget.map (pushoutObjGrayToPseudo f₁ f₂)).app _ y = x) ∨
      1 < U.dimension := by
  obtain ⟨j, x', hx', rfl⟩ := MarkedPresheaf.exists_mem_marked_of_isColimit
    (Functor.PushoutObjObj.ofHasPushout _ f₁ f₂).isPushout.isColimit hx
  obtain _ | ⟨_ | _⟩ := j
  · rw [PushoutCocone.condition_zero]
    exact exists_mem_marked_of_comp_eq (X := Y₁) (Y := X₂) _ _ _ (inl_pushoutObjGrayToPseudo f₁ f₂)
      (MarkedPresheaf.map_mem_marked
        (((Functor.curry.obj (markedTensorBifunctor.{u} true)).map f₁).app X₂) hx')
  · exact exists_mem_marked_of_comp_eq (X := Y₁) (Y := X₂) _ _ _ (inl_pushoutObjGrayToPseudo f₁ f₂)
      hx'
  · exact exists_mem_marked_of_comp_eq (X := X₁) (Y := Y₂) _ _ _ (inr_pushoutObjGrayToPseudo f₁ f₂)
      hx'

theorem MarkedDiagSet.Coinductive.weakEquivalence_pseudoPushoutProduct_iff (n : ℕ∞) (hn : n ≤ 1)
    {X₁ Y₁ X₂ Y₂ : MarkedDiagSet.{u}} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).ι) ↔
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι) := by
  have := weakEquivalence_of_isIso_forget_map_of_lt n _ fun U x hx =>
    (pushoutObjGrayToPseudo_marked f₁ f₂ U x hx).imp_right (lt_of_one_lt hn)
  have : WeakEquivalence ((MarkedDiagSet.toCoinductive n).map ((grayToPseudoLeft Y₁).app Y₂)) :=
    weakEquivalence_grayToPseudo n hn Y₁ Y₂
  have sq := congrArg (MarkedDiagSet.toCoinductive n).map
    (pushoutProduct_comp_grayToPseudo f₁ f₂)
  rw [Functor.map_comp, Functor.map_comp] at sq
  exact ⟨fun _ => weakEquivalence_of_postcomp_of_fac sq,
    fun _ => weakEquivalence_of_precomp_of_fac sq.symm⟩

theorem mono_pseudoPushoutProduct [Mono f₁] [Mono f₂] :
    Mono (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).ι := by
  have h := (MarkedPresheaf.mono_iff _).1 (mono_markedPushoutProduct f₁ f₂)
  have sq : MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ f₂).ι =
      MarkedPresheaf.forget.map (pushoutObjGrayToPseudo f₁ f₂) ≫ MarkedPresheaf.forget.map
        (Functor.PushoutObjObj.ofHasPushout
          (Functor.curry.obj (markedTensorBifunctor.{u} true)) f₁ f₂).ι :=
    (Category.comp_id _).symm.trans ((Functor.map_comp _ _ _).symm.trans
      ((congrArg _ (pushoutProduct_comp_grayToPseudo f₁ f₂)).trans (Functor.map_comp _ _ _)))
  refine (MarkedPresheaf.mono_iff _).2 ?_
  rw [← IsIso.inv_hom_id_assoc (MarkedPresheaf.forget.map (pushoutObjGrayToPseudo f₁ f₂))
    (MarkedPresheaf.forget.map _), ← sq]
  exact @mono_comp _ _ _ _ _ _ inferInstance _ h

end PushoutProduct

theorem isIso_conjugateEquiv_grayToPseudoRight_app (X : MarkedDiagSet.{u})
    {Z : MarkedDiagSet.{u}}
    (hZ : ∀ (U : Atom) (z : diagram Z.underlying U), 1 < U.dimension → z ∈ Z.marked U) :
    IsIso ((conjugateEquiv (tensorRightAdjunction true X) (tensorRightAdjunction false X)
      (grayToPseudoRight X)).app Z) :=
  isIso_conjugateEquiv_app_of_bijective _ _ _ Z fun T =>
    bijective_comp_of_isIso_forget_map (grayToPseudo T X) (grayToPseudo_marked T X) hZ

theorem isIso_conjugateEquiv_grayToPseudoLeft_app (X : MarkedDiagSet.{u})
    {Z : MarkedDiagSet.{u}}
    (hZ : ∀ (U : Atom) (z : diagram Z.underlying U), 1 < U.dimension → z ∈ Z.marked U) :
    IsIso ((conjugateEquiv (tensorLeftAdjunction true X) (tensorLeftAdjunction false X)
      (grayToPseudoLeft X)).app Z) :=
  isIso_conjugateEquiv_app_of_bijective _ _ _ Z fun T =>
    bijective_comp_of_isIso_forget_map (grayToPseudo X T) (grayToPseudo_marked X T) hZ

end Atoms.Diagrammatic
