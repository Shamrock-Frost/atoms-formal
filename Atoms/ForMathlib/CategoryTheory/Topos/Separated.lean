import Atoms.ForMathlib.CategoryTheory.Sites.LocallySurjective
import Atoms.ForMathlib.CategoryTheory.Sites.Separated
import Atoms.ForMathlib.CategoryTheory.Topos.Quasitopos

universe w' w v

namespace CategoryTheory

open Opposite Limits

variable {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}

section DependentProduct

variable {X Y : Cᵒᵖ ⥤ Type (max w v)} (f : X ⟶ Y)

theorem Over.hom_ext_rightAdjoint_pullback {E : Over X} (hE : Presieve.IsSeparated J E.left)
    {W₀ W : Over Y} (i : W₀ ⟶ W) [Presheaf.IsLocallySurjective J i.left]
    {u v : W ⟶ (Over.pullback f).rightAdjoint.obj E} (h : i ≫ u = i ≫ v) : u = v := by
  let adj := Adjunction.ofIsLeftAdjoint (Over.pullback f)
  apply (adj.homEquiv W E).symm.injective
  have h' := congrArg CommaMorphism.left (congrArg (adj.homEquiv W₀ E).symm h)
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_left_symm] at h'
  simp only [Over.comp_left] at h'
  exact Over.OverMorphism.ext (hE.hom_ext _ h')

theorem Presieve.isSeparated_rightAdjoint_pullback_obj_left (hY : IsSeparated J Y) {E : Over X}
    (hE : IsSeparated J E.left) : IsSeparated J ((Over.pullback f).rightAdjoint.obj E).left := by
  refine isSeparated_iff_locallyEq.2 fun c x y hxy => ?_
  let P := (Over.pullback f).rightAdjoint.obj E
  let S := Presheaf.equalizerSieve (F := P.left) x y
  let ι : S.functor ⋙ uliftFunctor.{w} ⟶ uliftYoneda.{w}.obj c.unop :=
    Functor.whiskerRight S.functorInclusion uliftFunctor.{w}
  have hS : Presheaf.IsLocallySurjective J ι :=
    ⟨fun {d} g => J.superset_covering (fun e h hh => ⟨ULift.up ⟨h ≫ g.down, hh⟩, rfl⟩)
      (J.pullback_stable g.down hxy)⟩
  have hxy' : ι ≫ uliftYonedaEquiv.symm x = ι ≫ uliftYonedaEquiv.symm y := by
    ext d ⟨g, hg⟩
    exact hg
  have hP : uliftYonedaEquiv.symm x ≫ P.hom = uliftYonedaEquiv.symm y ≫ P.hom :=
    hY.hom_ext ι (by rw [← Category.assoc, hxy', Category.assoc])
  let i : Over.mk (ι ≫ uliftYonedaEquiv.symm x ≫ P.hom) ⟶
      Over.mk (uliftYonedaEquiv.symm x ≫ P.hom) := Over.homMk ι
  have : Presheaf.IsLocallySurjective J i.left := hS
  exact uliftYonedaEquiv.symm.injective (congrArg CommaMorphism.left
    (Over.hom_ext_rightAdjoint_pullback f hE i (u := Over.homMk (uliftYonedaEquiv.symm x))
      (v := Over.homMk (uliftYonedaEquiv.symm y) hP.symm) (Over.OverMorphism.ext hxy')))

end DependentProduct

namespace SeparatedPresheaf

theorem isIso_unit_app {P : Cᵒᵖ ⥤ Type (max w v)} (hP : Presieve.IsSeparated J P) :
    IsIso ((adjunction J).unit.app P) := by
  rw [adjunction_unit_app]
  have (c : Cᵒᵖ) : IsIso ((toReflectionObj J P).app c) := (isIso_iff_bijective _).2
    ⟨fun x y h => hP.eq_of_locallyEq ((toReflectionObj_app_eq_iff x y).1 h),
      surjective_toReflectionObj_app P c⟩
  exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this

instance hasLimitsOfSize : HasLimitsOfSize.{max w v, max w v} (SeparatedPresheaf.{max w v} J) :=
  ⟨fun _ _ => inferInstance⟩

instance hasFiniteLimits : HasFiniteLimits (SeparatedPresheaf.{max w v} J) :=
  hasFiniteLimits_of_hasLimitsOfSize _

instance reflective :
    Reflective (ObjectProperty.ι (C := Cᵒᵖ ⥤ Type (max w v)) (Presieve.IsSeparated J))
    where
  L := reflection J
  adj := adjunction J

instance hasColimitsOfSize : HasColimitsOfSize.{w', max w v} (SeparatedPresheaf.{max w v} J) :=
  hasColimits_of_reflective (ObjectProperty.ι _)

instance hasFiniteColimits : HasFiniteColimits (SeparatedPresheaf.{max w v} J) :=
  hasFiniteColimits_of_hasColimitsOfSize.{max w v, max w v} _

section Pi

variable {X Y : SeparatedPresheaf.{max w v} J} (f : X ⟶ Y)

noncomputable def postPullbackIso :
    Over.post (ObjectProperty.ι _) ⋙ Over.pullback f.hom ≅
      Over.pullback f ⋙
        Over.post (ObjectProperty.ι (C := Cᵒᵖ ⥤ Type (max w v)) (Presieve.IsSeparated J)) :=
  conjugateIsoEquiv ((Over.mapPullbackAdj f.hom).comp (Over.postAdjunctionRight (adjunction J)))
    ((Over.postAdjunctionRight (adjunction J)).comp (Over.mapPullbackAdj f))
    (NatIso.ofComponents (fun A => Over.isoMk (Iso.refl _)
      ((Category.id_comp _).trans <|
        (congrArg (· ≫ (adjunction J).counit.app Y) ((reflection J).map_comp A.hom f.hom)).trans <|
          ((Category.assoc _ _ _).trans (congrArg ((reflection J).map A.hom ≫ ·)
            ((adjunction J).counit.naturality f))).trans (Category.assoc _ _ _).symm))
      fun _ => Over.OverMorphism.ext ((Category.comp_id _).trans (Category.id_comp _).symm))

noncomputable def pi : Over X ⥤ Over Y :=
  Over.post (ObjectProperty.ι _) ⋙ (Over.pullback f.hom).rightAdjoint ⋙
    Over.post (reflection J) ⋙ Over.map ((adjunction J).counit.app Y)

noncomputable def piIso : Over.post (ObjectProperty.ι _) ⋙ (Over.pullback f.hom).rightAdjoint ≅
    pi f ⋙ Over.post (ObjectProperty.ι (C := Cᵒᵖ ⥤ Type (max w v)) (Presieve.IsSeparated J)) :=
  NatIso.ofComponents (fun E =>
    letI η := (Over.postAdjunctionRight (adjunction J)).unit.app
      ((Over.pullback f.hom).rightAdjoint.obj ((Over.post (ObjectProperty.ι _)).obj E))
    haveI : IsIso ((Over.forget _).map η) :=
      isIso_unit_app (Presieve.isSeparated_rightAdjoint_pullback_obj_left f.hom Y.2 E.left.2)
    @asIso _ _ _ _ η (isIso_of_reflects_iso η (Over.forget _)))
    fun _ => (Over.postAdjunctionRight (adjunction J)).unit.naturality _

noncomputable def pullbackAdjunction : Over.pullback f ⊣ pi f :=
  Adjunction.restrictFullyFaithful (Adjunction.ofIsLeftAdjoint (Over.pullback f.hom))
    (Functor.FullyFaithful.over (X := Y) (ObjectProperty.ι _) (ObjectProperty.fullyFaithfulι _))
    (Functor.FullyFaithful.over (X := X) (ObjectProperty.ι _) (ObjectProperty.fullyFaithfulι _))
    (postPullbackIso f) (piIso f)

end Pi

section Classifier

variable (J)

def terminal : SeparatedPresheaf.{max w v} J :=
  ⟨(Functor.const Cᵒᵖ).obj PUnit.{max w v + 1}, fun _ _ _ _ _ _ _ _ => rfl⟩

def toTerminal (U : SeparatedPresheaf.{max w v} J) : U ⟶ terminal J :=
  ObjectProperty.homMk { app _ := ↾fun _ => PUnit.unit }

def omega : SeparatedPresheaf.{max w v} J :=
  ⟨(Functor.closedSieves J).toFunctor ⋙ uliftFunctor.{w},
    (Presieve.isSheaf_comp_uliftFunctor J (classifier_isSheaf J)).isSeparated⟩

def truth : terminal J ⟶ omega J :=
  ObjectProperty.homMk
    { app c := ↾fun _ => ULift.up ⟨(⊤ : Sieve c.unop), fun _ _ _ => trivial⟩
      naturality _ _ f := by
        ext
        exact ULift.ext _ _ (Subtype.ext Sieve.pullback_top.symm) }

instance mono_truth : Mono (truth J) :=
  (ObjectProperty.ι _).mono_of_mono_map ((NatTrans.mono_iff_mono_app _).2 fun _ =>
    (mono_iff_injective _).2 fun _ _ _ => rfl)

variable {J}

theorem injective_app {U X : SeparatedPresheaf.{max w v} J} (m : U ⟶ X) [Mono m] (c : Cᵒᵖ) :
    Function.Injective (m.hom.app c) :=
  (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
    ((ObjectProperty.ι _).map_mono m) c)

theorem exists_app_eq_of_imageSieve_mem {U X : SeparatedPresheaf.{max w v} J} (m : U ⟶ X)
    [StrongMono m] {c : Cᵒᵖ} (x : X.obj.obj c) (hx : Presheaf.imageSieve m.hom x ∈ J c.unop) :
    ∃ t, m.hom.app c t = x := by
  let G := (Subfunctor.range m.hom).sheafify J
  let Gs : SeparatedPresheaf.{max w v} J := ⟨G.toFunctor, fun _ S hS => (X.2 S hS).of_mono G.ι⟩
  let e : U ⟶ Gs := ObjectProperty.homMk (Subfunctor.lift m.hom (Subfunctor.le_sheafify J _))
  let i : Gs ⟶ X := ObjectProperty.homMk G.ι
  have he : Presheaf.IsLocallySurjective J e.hom :=
    ⟨fun {d} s => J.superset_covering (fun d' f hf => by
      obtain ⟨t, ht⟩ := hf
      exact ⟨t, Subtype.ext ht⟩) s.2⟩
  have : Epi e := ⟨fun {P} g h hgh => ObjectProperty.hom_ext _
    (P.2.hom_ext e.hom (congrArg (fun φ => φ.hom) hgh))⟩
  have sq : CommSq (𝟙 U) e m i := ⟨by rw [Category.id_comp]; rfl⟩
  have := StrongMono.rlp e (f := m)
  refine ⟨(sq.lift).hom.app c ⟨x, hx⟩, ?_⟩
  exact congrArg (fun φ : Gs ⟶ X => φ.hom.app c ⟨x, hx⟩) sq.fac_right

theorem isClosed_imageSieve {U X : SeparatedPresheaf.{max w v} J} (m : U ⟶ X) [StrongMono m]
    {c : Cᵒᵖ} (x : X.obj.obj c) : J.IsClosed (Presheaf.imageSieve m.hom x) := by
  intro d f hf
  rw [GrothendieckTopology.covers_iff, Presheaf.pullback_imageSieve] at hf
  obtain ⟨t, ht⟩ := exists_app_eq_of_imageSieve_mem m _ hf
  exact ⟨t, ht⟩

def classifyingMap {U X : SeparatedPresheaf.{max w v} J} (m : U ⟶ X) [StrongMono m] : X ⟶ omega J :=
  ObjectProperty.homMk
    { app c := ↾fun x => ULift.up ⟨Presheaf.imageSieve m.hom x, isClosed_imageSieve m x⟩
      naturality c c' f := by
        ext x
        refine ULift.ext _ _ (Subtype.ext (Sieve.ext fun d g => ?_))
        change (∃ t, m.hom.app _ t = X.obj.map g.op (X.obj.map f x)) ↔
          ∃ t, m.hom.app _ t = X.obj.map (g ≫ f.unop).op x
        rw [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] }

theorem isPullback_classifyingMap {U X : SeparatedPresheaf.{max w v} J} (m : U ⟶ X) [StrongMono m] :
    IsPullback m (toTerminal J U) (classifyingMap m) (truth J) := by
  have w : m ≫ classifyingMap m = toTerminal J U ≫ truth J := by
    ext c u
    refine ULift.ext _ _ (Subtype.ext (Sieve.ext fun d f =>
      iff_of_true ⟨U.obj.map f.op u, ?_⟩ trivial))
    exact NatTrans.naturality_apply m.hom f.op u
  refine IsPullback.of_map (ObjectProperty.ι _) w (IsPullback.of_forall_isPullback_app fun c =>
    (Types.isPullback_iff _ _ _ _).2 ⟨congrArg (fun φ => φ.hom.app c) w,
      fun x y h => injective_app m c h.1, fun x _ h => ?_⟩)
  obtain ⟨t, ht⟩ : (Presheaf.imageSieve m.hom x).arrows (𝟙 c.unop) := by
    have h' := congrArg (fun s => s.down.1) h
    change Presheaf.imageSieve m.hom x = ⊤ at h'
    rw [h']
    trivial
  exact ⟨t, ht.trans (by simp), rfl⟩

theorem classifyingMap_unique {U X : SeparatedPresheaf.{max w v} J} (m : U ⟶ X) [StrongMono m]
    {χ₀' : U ⟶ terminal J} {χ' : X ⟶ omega J} (hχ' : IsPullback m χ₀' χ' (truth J)) :
    χ' = classifyingMap m := by
  ext c x
  refine ULift.ext _ _ (Subtype.ext (Sieve.ext fun d f => ?_))
  have hp := (Types.isPullback_iff _ _ _ _).1 ((hχ'.map (ObjectProperty.ι _)).app (op d))
  have hn : (χ'.hom.app (op d) (X.obj.map f.op x)).down.1 =
      (χ'.hom.app c x).down.1.pullback f :=
    congrArg (fun s => s.down.1) (NatTrans.naturality_apply χ'.hom f.op x)
  change Sieve.arrows (χ'.hom.app c x).down.1 f ↔ ∃ t, m.hom.app (op d) t = X.obj.map f.op x
  constructor
  · intro h
    have h₂ : (χ'.hom.app (op d) (X.obj.map f.op x)).down.1 = (⊤ : Sieve d) :=
      hn.trans ((Sieve.mem_iff_pullback_eq_top f).1 h)
    obtain ⟨t, ht, -⟩ :=
      hp.2.2 (X.obj.map f.op x) PUnit.unit (ULift.ext _ _ (Subtype.ext h₂))
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    have h₁ : (χ'.hom.app (op d) (m.hom.app (op d) t)).down.1 = (⊤ : Sieve d) :=
      congrArg (fun s => s.down.1) (ConcreteCategory.congr_hom hp.1 t)
    rw [ht] at h₁
    exact (Sieve.mem_iff_pullback_eq_top f).2 (hn.symm.trans h₁)

def strongClassifier : Subobject.StrongClassifier (SeparatedPresheaf.{max w v} J) where
  Ω₀ := terminal J
  Ω := omega J
  truth := truth J
  χ₀ := toTerminal J
  χ m _ := classifyingMap m
  isPullback m _ := isPullback_classifyingMap m
  uniq m _ _ _ h := classifyingMap_unique m h

end Classifier

instance quasitopos : Quasitopos (SeparatedPresheaf.{max w v} J) where
  isLeftAdjoint_pullback f := (pullbackAdjunction f).isLeftAdjoint
  nonempty_strongClassifier := ⟨strongClassifier⟩

end SeparatedPresheaf

end CategoryTheory
