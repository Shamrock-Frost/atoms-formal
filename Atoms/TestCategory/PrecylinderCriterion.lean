import Atoms.TestCategory.Presheaf.Transport

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

structure FunctorialPrecylinder (A : Type u) [Category.{u} A] where
  I : A ⥤ A
  ι : Bool → (𝟭 A ⟶ I)

namespace FunctorialPrecylinder

variable {A : Type u} [SmallCategory A] (P : FunctorialPrecylinder A)

structure Augmentation where
  σ (a : A) : P.I.obj a ⟶ a
  ι_σ (ε : Bool) (a : A) : (P.ι ε).app a ≫ σ a = 𝟙 a

attribute [reassoc (attr := simp)] Augmentation.ι_σ

variable {P} in
@[reassoc (attr := simp)]
theorem Augmentation.ι_map_σ (σ : P.Augmentation) (ε : Bool) {a b : A} (β : b ⟶ a) :
    (P.ι ε).app b ≫ P.I.map β ≫ σ.σ a = β := by
  rw [← NatTrans.naturality_assoc]
  simp

structure IsSeparating : Prop where
  mono (a : A) : Mono ((P.ι false).app a)
  ne {a b : A} (f g : b ⟶ a) : f ≫ (P.ι true).app a ≠ g ≫ (P.ι false).app a
  map_ne {a a' b : A} (α : a ⟶ a') (f : b ⟶ P.I.obj a)
    (hf : ∀ g : b ⟶ a, f ≠ g ≫ (P.ι false).app a) (g : b ⟶ a') :
    f ≫ P.I.map α ≠ g ≫ (P.ι false).app a'

variable {P}

@[simps]
def overI (σ : P.Augmentation) (a : A) : Over a ⥤ Over a where
  obj b := Over.mk (P.I.map b.hom ≫ σ.σ a)
  map f := Over.homMk (P.I.map f.left) (by
    simp only [Over.mk_hom, ← P.I.map_comp_assoc, Over.w])
  map_id _ := Over.OverMorphism.ext (P.I.map_id _)
  map_comp _ _ := Over.OverMorphism.ext (P.I.map_comp _ _)

@[simps]
def over (σ : P.Augmentation) (a : A) : FunctorialPrecylinder (Over a) where
  I := overI σ a
  ι ε :=
    { app b := Over.homMk ((P.ι ε).app b.left) (σ.ι_map_σ ε b.hom)
      naturality _ _ f := Over.OverMorphism.ext ((P.ι ε).naturality f.left) }

theorem IsSeparating.over {P : FunctorialPrecylinder A} (hP : P.IsSeparating)
    (σ : P.Augmentation) (a : A) : (P.over σ a).IsSeparating where
  mono b := Over.mono_of_mono_left (hk := hP.mono b.left) _
  ne f g h := hP.ne f.left g.left (congrArg CommaMorphism.left h)
  map_ne α f hf g h := hP.map_ne α.left f.left
    (fun g' hg' => hf (Over.homMk g' (by
      have := Over.w f
      rw [hg'] at this
      change (g' ≫ _) ≫ P.I.map _ ≫ σ.σ a = _ at this
      rwa [Category.assoc, σ.ι_map_σ] at this)) (Over.OverMorphism.ext hg'))
    g.left (congrArg CommaMorphism.left h)

end FunctorialPrecylinder

section Extension

variable {A : Type u} [SmallCategory A] {C : Type u} [Category.{u} C] [HasTerminal C]

private theorem exists_map_obj_eq {a b : A} (i : a ⟶ b) (p : Over b) (g : p.left ⟶ a)
    (h : p.hom = g ≫ i) : ∃ x, (Over.map i).obj x = p := by
  obtain ⟨l, ⟨⟨⟩⟩, hom⟩ := p
  change l ⟶ a at g
  change hom = g ≫ i at h
  subst h
  exact ⟨Over.mk g, rfl⟩

private theorem functor_eq_of_sieve {a b : A} (i : a ⟶ b) [Mono i] (F G : Over b ⥤ C)
    (h : Over.map i ⋙ F = Over.map i ⋙ G)
    (hF : ∀ p : Over b, (∀ g, p.hom ≠ g ≫ i) → F.obj p = ⊤_ C)
    (hG : ∀ p : Over b, (∀ g, p.hom ≠ g ≫ i) → G.obj p = ⊤_ C) : F = G := by
  have hobj : ∀ p, F.obj p = G.obj p := fun p => by
    by_cases hp : ∃ g, p.hom = g ≫ i
    · obtain ⟨g, hg⟩ := hp
      obtain ⟨x, rfl⟩ := exists_map_obj_eq i p g hg
      exact Functor.congr_obj h _
    · push Not at hp
      rw [hF p hp, hG p hp]
  refine CategoryTheory.Functor.ext hobj fun p q f => ?_
  by_cases hq : ∃ g, q.hom = g ≫ i
  · obtain ⟨g, hg⟩ := hq
    obtain ⟨y, rfl⟩ := exists_map_obj_eq i q g hg
    obtain ⟨x, rfl⟩ := exists_map_obj_eq i p (f.left ≫ y.hom) (by
      rw [← Over.w f, Category.assoc]
      rfl)
    have hf : f = (Over.map i).map (Over.homMk f.left (by
        rw [← cancel_mono i, Category.assoc]
        exact Over.w f) : x ⟶ y) :=
      Over.OverMorphism.ext rfl
    rw [hf]
    exact Functor.congr_hom h _
  · push Not at hq
    rw [← cancel_mono (eqToHom (hF q hq))]
    exact terminal.hom_ext _ _

private noncomputable def glueFunctor {a b : A} (i : a ⟶ b) [Mono i] (v : Over a ⥤ C) :
    Over b ⥤ C :=
  (elementsYonedaCatIso A b).inv.toFunctor ⋙
    NatTrans.extendElementsFunctor (yoneda.map i) ((elementsYonedaCatIso A a).hom.toFunctor ⋙ v)

private theorem map_comp_glueFunctor {a b : A} (i : a ⟶ b) [Mono i] (v : Over a ⥤ C) :
    Over.map i ⋙ glueFunctor i v = v := by
  change (elementsYonedaCatIso A a).inv.toFunctor ⋙ ((NatTrans.mapElements (yoneda.map i)).op ⋙
    NatTrans.extendElementsFunctor (yoneda.map i)
      ((elementsYonedaCatIso A a).hom.toFunctor ⋙ v)) = v
  exact congrArg ((elementsYonedaCatIso A a).inv.toFunctor ⋙ ·)
    (NatTrans.mapElements_op_comp_extendElementsFunctor (yoneda.map i) _)

private theorem glueFunctor_obj {a b : A} (i : a ⟶ b) [Mono i] (v : Over a ⥤ C) (p : Over b)
    (hp : ∀ g, p.hom ≠ g ≫ i) : (glueFunctor i v).obj p = ⊤_ C :=
  NatTrans.extendElementsObj_of_not_mem _ _ fun ⟨y, hy⟩ => hp y hy.symm

end Extension

namespace FunctorialPrecylinder

variable {A : Type u} [SmallCategory A] {P : FunctorialPrecylinder A}

variable (hP : P.IsSeparating) (C : Cat.{u, u}) [HasTerminal C]

private noncomputable def glue (a : A) (v : ((nerveFunctor A).obj C).obj (op a)) :
    ((nerveFunctor A).obj C).obj (op (P.I.obj a)) :=
  haveI := hP.mono a
  (glueFunctor ((P.ι false).app a) (nerveElementFunctor C v)).toCatHom

private theorem glue_map {a a' : A} (α : a ⟶ a') (v : ((nerveFunctor A).obj C).obj (op a))
    (v' : ((nerveFunctor A).obj C).obj (op a'))
    (h : ((nerveFunctor A).obj C).map α.op v' = v) :
    ((nerveFunctor A).obj C).map (P.I.map α).op (glue hP C a' v') = glue hP C a v := by
  have := hP.mono a
  have := hP.mono a'
  refine Cat.Hom.ext (functor_eq_of_sieve ((P.ι false).app a) _ _ ?_ ?_ ?_)
  · change (Over.map ((P.ι false).app a) ⋙ Over.map (P.I.map α)) ⋙
      glueFunctor ((P.ι false).app a') (nerveElementFunctor C v') =
      Over.map ((P.ι false).app a) ⋙ glueFunctor ((P.ι false).app a) (nerveElementFunctor C v)
    rw [← Over.mapComp_eq, ← (P.ι false).naturality, Functor.id_map, Over.mapComp_eq,
      Functor.assoc, map_comp_glueFunctor, map_comp_glueFunctor, ← h]
    rfl
  · exact fun p hp => glueFunctor_obj _ _ _ (hP.map_ne α p.hom hp)
  · exact fun p hp => glueFunctor_obj _ _ _ hp

private theorem map_ι_true_glue (a : A) (v : ((nerveFunctor A).obj C).obj (op a)) :
    ((nerveFunctor A).obj C).map ((P.ι true).app a).op (glue hP C a v) =
      ((Functor.const (Over a)).obj (⊤_ C)).toCatHom := by
  have := hP.mono a
  have h : ∀ x : Over a, (Over.map ((P.ι true).app a) ⋙
      glueFunctor ((P.ι false).app a) (nerveElementFunctor C v)).obj x = ⊤_ C :=
    fun x => glueFunctor_obj _ _ _ (fun g => hP.ne x.hom g)
  have key : Over.map ((P.ι true).app a) ⋙
      glueFunctor ((P.ι false).app a) (nerveElementFunctor C v) =
        (Functor.const (Over a)).obj (⊤_ C) := by
    refine CategoryTheory.Functor.ext h fun x y f => ?_
    rw [← cancel_mono (eqToHom (h y))]
    exact terminal.hom_ext _ _
  exact Cat.Hom.ext key

private noncomputable def cylElements :
    (((nerveFunctor A).obj C).Elements)ᵒᵖ ⥤ (((nerveFunctor A).obj C).Elements)ᵒᵖ where
  obj p := op ⟨op (P.I.obj (unop p.unop.1)), glue hP C (unop p.unop.1) p.unop.2⟩
  map f := CategoryOfElements.opHomMk (P.I.map f.unop.1.unop) (glue_map hP C _ _ _ f.unop.2)
  map_id _ := CategoryOfElements.op_hom_ext (P.I.map_id _)
  map_comp _ _ := CategoryOfElements.op_hom_ext (P.I.map_comp _ _)

private noncomputable def cylElementsι₀ : 𝟭 _ ⟶ cylElements hP C where
  app p := CategoryOfElements.opHomMk ((P.ι false).app (unop p.unop.1))
    (haveI := hP.mono (unop p.unop.1); Cat.Hom.ext (map_comp_glueFunctor _ _))
  naturality _ _ f := CategoryOfElements.op_hom_ext ((P.ι false).naturality f.unop.1.unop)

private noncomputable def constElements : A ⥤ (((nerveFunctor A).obj C).Elements)ᵒᵖ where
  obj a := op ⟨op a, ((Functor.const (Over a)).obj (⊤_ C)).toCatHom⟩
  map α := CategoryOfElements.opHomMk α rfl

private noncomputable def cylElementsι₁ :
    (CategoryOfElements.π ((nerveFunctor A).obj C)).leftOp ⋙ constElements C ⟶
      cylElements hP C where
  app p := CategoryOfElements.opHomMk ((P.ι true).app (unop p.unop.1))
    (map_ι_true_glue hP C _ _)
  naturality _ _ f := CategoryOfElements.op_hom_ext ((P.ι true).naturality f.unop.1.unop)

end FunctorialPrecylinder

namespace BasicLocalizer

variable (𝒲 : BasicLocalizer.{u}) {A : Type u} [SmallCategory A]

theorem wPsh_terminal_from_nerveFunctor_obj (P : FunctorialPrecylinder A) (hP : P.IsSeparating)
    (C : Cat.{u, u}) [HasTerminal C] :
    𝒲.wPsh A (terminal.from ((nerveFunctor A).obj C)) := by
  let r := (CategoryOfElements.π ((nerveFunctor A).obj C)).leftOp
  let j := FunctorialPrecylinder.constElements (A := A) C
  have hD : 𝒲.W (P.cylElements hP C).toCatHom :=
    (𝒲.W_iff_of_natTrans (u := 𝟙 (Cat.of _)) (v := (P.cylElements hP C).toCatHom)
      (P.cylElementsι₀ hP C)).1 (𝒲.W.id_mem _)
  have hrj : 𝒲.W (r ⋙ j).toCatHom :=
    (𝒲.W_iff_of_natTrans (u := (r ⋙ j).toCatHom) (v := (P.cylElements hP C).toCatHom)
      (P.cylElementsι₁ hP C)).2 hD
  have hr : 𝒲.W r.toCatHom := 𝒲.W.of_retract (f := r.toCatHom) (g := (r ⋙ j).toCatHom)
    { i := Arrow.homMk (𝟙 _) j.toCatHom (by rfl)
      r := Arrow.homMk (𝟙 _) r.toCatHom (by rfl)
      retract := by rfl } hrj
  refine 𝒲.W.of_postcomp _ (elementsTerminalHom A) (𝒲.W_elementsTerminalHom A) ?_
  exact hr

theorem isLocalTest_of_isSeparating (P : FunctorialPrecylinder A) (σ : P.Augmentation)
    (hP : P.IsSeparating) : 𝒲.IsLocalTest A :=
  𝒲.isLocalTest_of_locallyAspherical_nerveFunctor_obj A fun C _ a =>
    have : HasTerminal (Cat.of (Over a)) := Over.mkIdTerminal.hasTerminal
    (𝒲.pshAspherical_nerveFunctor_over_iff A a C).1
      ((𝒲.pshAspherical_iff_wPsh_terminal_from (Over a) (𝒲.terminal_aspherical (Cat.of (Over a)))
        _).2 (𝒲.wPsh_terminal_from_nerveFunctor_obj (P.over σ a) (hP.over σ a) C))

theorem isTest_of_isSeparating [HasTerminal A] (P : FunctorialPrecylinder A)
    (σ : P.Augmentation) (hP : P.IsSeparating) : 𝒲.IsTest A :=
  (𝒲.isTest_iff_aspherical_and_isLocalTest A).2
    ⟨𝒲.terminal_aspherical (Cat.of A), 𝒲.isLocalTest_of_isSeparating P σ hP⟩

end BasicLocalizer

end Atoms.TestCategory
