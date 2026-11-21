import Atoms.ForMathlib.CategoryTheory.EqToHom
import Atoms.TestCategory.BasicLocalizer.GrothendieckConstruction

open CategoryTheory Limits

attribute [local implicit_reducible] WidePushoutShape.wideSpan Grothendieck.ι

namespace Atoms.TestCategory

universe u

namespace BasicLocalizer

variable {A A' B B' : Cat.{u, u}} {α : A ⟶ A'} {i : A ⟶ B} {i' : A' ⟶ B'} {β : B ⟶ B'}

def squareComparison (h : CommSq α i i' β) :
    Cat.of (Grothendieck (Limits.span i α)) ⟶ B' :=
  (Grothendieck.spanFunctorFrom (i ≫ β).toFunctor β.toFunctor i'.toFunctor (𝟙 _)
    (eqToHom (congrArg Cat.Hom.toFunctor h.w.symm))).toCatHom

theorem ι_right_comp_squareComparison (h : CommSq α i i' β) :
    (Grothendieck.ι (Limits.span i α) .right).toCatHom ≫ squareComparison h = i' :=
  Cat.Hom.ext (Grothendieck.ι_right_comp_spanFunctorFrom _ _ _ _ _)

section Naturality

variable {A₁ A₁' B₁ B₁' A₂ A₂' B₂ B₂' : Cat.{u, u}} {α₁ : A₁ ⟶ A₁'} {i₁ : A₁ ⟶ B₁}
  {i₁' : A₁' ⟶ B₁'} {β₁ : B₁ ⟶ B₁'} {α₂ : A₂ ⟶ A₂'} {i₂ : A₂ ⟶ B₂} {i₂' : A₂' ⟶ B₂'}
  {β₂ : B₂ ⟶ B₂'}

theorem map_comp_squareComparison (h₁ : CommSq α₁ i₁ i₁' β₁) (h₂ : CommSq α₂ i₂ i₂' β₂)
    (a : span i₁ α₁ ⟶ span i₂ α₂) (b : B₁' ⟶ B₂') (hl : a.app .left ≫ β₂ = β₁ ≫ b)
    (hr : a.app .right ≫ i₂' = i₁' ≫ b) :
    (Grothendieck.map a).toCatHom ≫ squareComparison h₂ = squareComparison h₁ ≫ b := by
  have hf : i₁ ≫ a.app .left = a.app .zero ≫ i₂ := a.naturality WalkingSpan.Hom.fst
  have e₀ : a.app .zero ≫ i₂ ≫ β₂ = (i₁ ≫ β₁) ≫ b := by
    rw [← Category.assoc, ← hf, Category.assoc, hl, Category.assoc]
  have hobj : ∀ W, ((Grothendieck.map a).toCatHom ≫ squareComparison h₂).toFunctor.obj W =
      (squareComparison h₁ ≫ b).toFunctor.obj W := by
    rintro ⟨(_ | (_ | _)), x⟩
    · exact Functor.congr_obj (congrArg Cat.Hom.toFunctor e₀) x
    · exact Functor.congr_obj (congrArg Cat.Hom.toFunctor hl) x
    · exact Functor.congr_obj (congrArg Cat.Hom.toFunctor hr) x
  refine Cat.Hom.ext (Grothendieck.spanFunctor_ext hobj (fun c x y φ => ?_) (fun x => ?_)
    (fun x => ?_))
  · have hm : (Grothendieck.map a).map ((Grothendieck.ι _ c).map φ) =
        (Grothendieck.ι _ c).map ((a.app c).toFunctor.map φ) :=
      (Category.comp_id _).symm.trans (((Grothendieck.ιCompMap a c).hom.naturality φ).trans
        (Category.id_comp _))
    rcases c with _ | (_ | _)
    · have h2 : (squareComparison h₁ ≫ b).toFunctor.map ((Grothendieck.ι _ .zero).map φ) =
          ((i₁ ≫ β₁) ≫ b).toFunctor.map φ :=
        congrArg b.toFunctor.map (Grothendieck.spanFunctorFrom_map_ι _ _ _ _ _ _ _)
      exact (congrArg (· ≫ _) ((congrArg (squareComparison h₂).toFunctor.map hm).trans
        (Grothendieck.spanFunctorFrom_map_ι _ _ _ _ _ _ _))).trans <| ((comp_eqToHom_iff _ _ _).2
        ((Functor.congr_hom (congrArg Cat.Hom.toFunctor e₀) φ).trans
          (Category.assoc _ _ _).symm)).trans (congrArg (_ ≫ ·) h2.symm)
    · have h2 : (squareComparison h₁ ≫ b).toFunctor.map ((Grothendieck.ι _ .left).map φ) =
          (β₁ ≫ b).toFunctor.map φ :=
        congrArg b.toFunctor.map (Grothendieck.spanFunctorFrom_map_ι _ _ _ _ _ _ _)
      exact (congrArg (· ≫ _) ((congrArg (squareComparison h₂).toFunctor.map hm).trans
        (Grothendieck.spanFunctorFrom_map_ι _ _ _ _ _ _ _))).trans <| ((comp_eqToHom_iff _ _ _).2
        ((Functor.congr_hom (congrArg Cat.Hom.toFunctor hl) φ).trans
          (Category.assoc _ _ _).symm)).trans (congrArg (_ ≫ ·) h2.symm)
    · have h2 : (squareComparison h₁ ≫ b).toFunctor.map ((Grothendieck.ι _ .right).map φ) =
          (i₁' ≫ b).toFunctor.map φ :=
        congrArg b.toFunctor.map (Grothendieck.spanFunctorFrom_map_ι _ _ _ _ _ _ _)
      exact (congrArg (· ≫ _) ((congrArg (squareComparison h₂).toFunctor.map hm).trans
        (Grothendieck.spanFunctorFrom_map_ι _ _ _ _ _ _ _))).trans <| ((comp_eqToHom_iff _ _ _).2
        ((Functor.congr_hom (congrArg Cat.Hom.toFunctor hr) φ).trans
          (Category.assoc _ _ _).symm)).trans (congrArg (_ ≫ ·) h2.symm)
  · have hY : (squareComparison h₁ ≫ b).toFunctor.map
        ((Grothendieck.ιNatTrans (F := span i₁ α₁) WalkingSpan.Hom.fst).app x) = 𝟙 _ :=
      (congrArg b.toFunctor.map (Grothendieck.spanFunctorFrom_map_fst _ _ _ _ _ x)).trans
        (b.toFunctor.map_id _)
    have hG : ((Grothendieck.map a).toCatHom ≫ squareComparison h₂).toFunctor.map
        ((Grothendieck.ιNatTrans (F := span i₁ α₁) WalkingSpan.Hom.fst).app x) =
        𝟙 _ ≫ β₂.toFunctor.map ((eqToHom (a.naturality WalkingSpan.Hom.fst).symm).toNatTrans.app x ≫
          (a.app .left).toFunctor.map (𝟙 _)) := rfl
    simp only [Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app, Category.id_comp] at hG
    rw [(a.app WalkingSpan.left).toFunctor.map_id] at hG
    exact comp_eqToHom_eq_eqToHom_comp _ _
      ⟨_, hG.trans ((congrArg β₂.toFunctor.map (Category.comp_id _)).trans (eqToHom_map _ _))⟩
      ⟨rfl, hY.trans (eqToHom_refl _ _).symm⟩
  · have hY : (squareComparison h₁ ≫ b).toFunctor.map
        ((Grothendieck.ιNatTrans (F := span i₁ α₁) WalkingSpan.Hom.snd).app x) =
        b.toFunctor.map ((eqToHom (congrArg Cat.Hom.toFunctor h₁.w.symm)).app x) :=
      congrArg b.toFunctor.map (Grothendieck.spanFunctorFrom_map_snd _ _ _ _ _ x)
    have hG : ((Grothendieck.map a).toCatHom ≫ squareComparison h₂).toFunctor.map
        ((Grothendieck.ιNatTrans (F := span i₁ α₁) WalkingSpan.Hom.snd).app x) =
        (eqToHom (congrArg Cat.Hom.toFunctor h₂.w.symm)).app ((a.app .zero).toFunctor.obj x) ≫
          i₂'.toFunctor.map ((eqToHom (a.naturality WalkingSpan.Hom.snd).symm).toNatTrans.app x ≫
          (a.app .right).toFunctor.map (𝟙 _)) := rfl
    simp only [Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app] at hG hY
    rw [(a.app WalkingSpan.right).toFunctor.map_id] at hG
    exact comp_eqToHom_eq_eqToHom_comp _ _ ⟨_, hG.trans
      (eqToHom_comp_map_eqToHom_comp_id (C := ↥((span i₂ α₂).obj .right)) _ _ _)⟩
      ⟨_, hY.trans (eqToHom_map _ _)⟩

end Naturality

variable (𝒲 : BasicLocalizer.{u})

def IsHomotopyCocartesian (h : CommSq α i i' β) : Prop :=
  𝒲.W (squareComparison h)

section IdentitySpan

variable (α : A ⟶ A')

private def collapse :
    Grothendieck (span (𝟙 A) α) ⥤ Grothendieck (span (𝟙 A) α) :=
  Grothendieck.spanFunctorFrom (Grothendieck.ι (span (𝟙 A) α) .zero)
    (Grothendieck.ι (span (𝟙 A) α) .zero) (Grothendieck.ι (span (𝟙 A) α) .right) (𝟙 _)
    (Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd)

private def retraction : Grothendieck (span (𝟙 A) α) ⥤ ↥A' :=
  Grothendieck.spanFunctorFrom α.toFunctor α.toFunctor (𝟭 _) (𝟙 _) (𝟙 _)

private def collapseToId : collapse α ⟶ 𝟭 _ :=
  Grothendieck.spanNatTransMk
    (fun
      | ⟨.zero, _⟩ => 𝟙 _
      | ⟨.left, a⟩ => (Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.fst).app a
      | ⟨.right, _⟩ => 𝟙 _)
    (by
      rintro (_ | (_ | _)) x y φ
      all_goals simp only [collapse, Grothendieck.spanFunctorFrom_map_ι]
      · exact (Category.comp_id _).trans (Category.id_comp _).symm
      · exact (Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.fst).naturality φ
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (fun x => by
      have h : (collapse α).map
          ((Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.fst).app x) = 𝟙 _ :=
        (Category.id_comp _).trans ((Grothendieck.ι (span (𝟙 A) α) .zero).map_id x)
      exact congrArg (· ≫ _) h)
    (fun x => by
      have h : (collapse α).map
          ((Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd).app x) =
            (Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd).app x :=
        (congrArg (_ ≫ ·) ((Grothendieck.ι (span (𝟙 A) α) .right).map_id _)).trans
          (Category.comp_id _)
      exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm))

private def collapseToRetraction :
    collapse α ⟶ retraction α ⋙ Grothendieck.ι (span (𝟙 A) α) .right :=
  Grothendieck.spanNatTransMk
    (fun
      | ⟨.zero, a⟩ => (Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd).app a
      | ⟨.left, a⟩ => (Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd).app a
      | ⟨.right, _⟩ => 𝟙 _)
    (by
      rintro (_ | (_ | _)) x y φ
      all_goals simp only [collapse, retraction, Functor.comp_map,
        Grothendieck.spanFunctorFrom_map_ι]
      · exact (Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd).naturality φ
      · exact (Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd).naturality φ
      · exact (Category.comp_id _).trans (Category.id_comp _).symm)
    (fun x => by
      have h₁ : (collapse α).map
          ((Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.fst).app x) = 𝟙 _ :=
        (Category.id_comp _).trans ((Grothendieck.ι (span (𝟙 A) α) .zero).map_id x)
      have h₂ : (retraction α ⋙ Grothendieck.ι (span (𝟙 A) α) .right).map
          ((Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.fst).app x) = 𝟙 _ :=
        (congrArg (Grothendieck.ι (span (𝟙 A) α) .right).map
          ((Category.id_comp _).trans (α.toFunctor.map_id x))).trans
          ((Grothendieck.ι (span (𝟙 A) α) .right).map_id _)
      exact (congrArg (· ≫ _) h₁).trans <| (Category.id_comp _).trans <|
        (Category.comp_id _).symm.trans (congrArg (_ ≫ ·) h₂.symm))
    (fun x => by
      have h₁ : (collapse α).map
          ((Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd).app x) =
            (Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd).app x :=
        (congrArg (_ ≫ ·) ((Grothendieck.ι (span (𝟙 A) α) .right).map_id _)).trans
          (Category.comp_id _)
      have h₂ : (retraction α ⋙ Grothendieck.ι (span (𝟙 A) α) .right).map
          ((Grothendieck.ιNatTrans (F := span (𝟙 A) α) WalkingSpan.Hom.snd).app x) = 𝟙 _ :=
        (congrArg (Grothendieck.ι (span (𝟙 A) α) .right).map (Category.id_comp _)).trans
          ((Grothendieck.ι (span (𝟙 A) α) .right).map_id _)
      exact (Category.comp_id _).trans <| h₁.trans <|
        (Category.comp_id _).symm.trans (congrArg (_ ≫ ·) h₂.symm))

private theorem W_ι_right_identitySpan :
    𝒲.W (Grothendieck.ι (span (𝟙 A) α) .right).toCatHom := by
  refine 𝒲.W_of_comp_eq_id_of_W (r := (retraction α).toCatHom)
    (Cat.Hom.ext (Grothendieck.ι_right_comp_spanFunctorFrom _ _ _ _ _)) ?_
  have h : 𝒲.W (collapse α).toCatHom :=
    (𝒲.W_iff_of_natTrans (u := (collapse α).toCatHom) (v := 𝟙 _) (collapseToId α)).2
      (𝒲.W.id_mem _)
  exact (𝒲.W_iff_of_natTrans (u := (collapse α).toCatHom)
    (v := (retraction α).toCatHom ≫ (Grothendieck.ι (span (𝟙 A) α) .right).toCatHom)
    (collapseToRetraction α)).1 h

end IdentitySpan

theorem W_grothendieck_span_ι_right (hi : 𝒲.W i) (α : A ⟶ A') :
    𝒲.W ((Grothendieck.ι (Limits.span i α) Limits.WalkingSpan.right).toCatHom) := by
  let a : span (𝟙 A) α ⟶ span i α :=
    spanHomMk (𝟙 A) i (𝟙 A') rfl ((Category.comp_id _).trans (Category.id_comp _).symm)
  have ha : 𝒲.W (Grothendieck.map a).toCatHom :=
    𝒲.W_grothendieckMap_of_type a (by
      rintro (_ | (_ | _))
      exacts [𝒲.W.id_mem _, hi, 𝒲.W.id_mem _])
  exact (𝒲.W_iff_of_natTrans (v := (Grothendieck.ι (span i α) .right).toCatHom)
    (Grothendieck.ιCompMap a .right).hom).1 (𝒲.W.comp_mem _ _ (𝒲.W_ι_right_identitySpan α) ha)

theorem isHomotopyCocartesian_of_W (h : CommSq α i i' β) (hi : 𝒲.W i) (hi' : 𝒲.W i') :
    𝒲.IsHomotopyCocartesian h :=
  𝒲.W.of_precomp _ _ (𝒲.W_grothendieck_span_ι_right hi α)
    ((ι_right_comp_squareComparison h).symm ▸ hi')

theorem W_of_isHomotopyCocartesian (h : CommSq α i i' β) (hh : 𝒲.IsHomotopyCocartesian h)
    (hi : 𝒲.W i) : 𝒲.W i' :=
  ι_right_comp_squareComparison h ▸ 𝒲.W.comp_mem _ _ (𝒲.W_grothendieck_span_ι_right hi α) hh

end BasicLocalizer

end Atoms.TestCategory
