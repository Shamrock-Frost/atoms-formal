import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FunctionSpace
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.KanComplex

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty Opposite
  MonoidalCategory MonoidalClosed CartesianMonoidalCategory

universe u

namespace SSet

section Evaluation

noncomputable def evalVertex {A : SSet.{u}} (a : A _⦋0⦌) (X : SSet.{u}) :
    (ihom A).obj X ⟶ X :=
  lift (stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm a) (𝟙 _) ≫ (ihom.ev A).app X

lemma comp_evalVertex {A X Z : SSet.{u}} (a : A _⦋0⦌) (f : Z ⟶ (ihom A).obj X) :
    f ≫ evalVertex a X =
      lift (stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm a) (𝟙 Z) ≫ uncurry f := by
  rw [evalVertex, uncurry_eq, ← Category.assoc, ← Category.assoc, comp_lift, lift_whiskerLeft,
    Category.comp_id, Category.id_comp, ← Category.assoc,
    stdSimplex.isTerminalObj₀.hom_ext (f ≫ _) (stdSimplex.isTerminalObj₀.from Z)]

@[reassoc]
lemma ihom_map_comp_evalVertex {A X Y : SSet.{u}} (a : A _⦋0⦌) (p : X ⟶ Y) :
    (ihom A).map p ≫ evalVertex a Y = evalVertex a X ≫ p := by
  rw [comp_evalVertex, uncurry_ihom_map, evalVertex, Category.assoc]

@[reassoc]
lemma pre_app_comp_evalVertex {A B X : SSet.{u}} (i : A ⟶ B) (a : A _⦋0⦌) :
    (pre i).app X ≫ evalVertex a X = evalVertex (i.app _ a) X := by
  rw [comp_evalVertex, uncurry_pre, ← Category.assoc, lift_whiskerRight, Category.assoc,
    yonedaEquiv_symm_comp, evalVertex]

end Evaluation

section ObjectwiseCore

def objectwiseCore (A X : SSet.{u}) : ((ihom A).obj X).Subcomplex where
  obj n := {σ | ∀ a : A _⦋0⦌, (evalVertex a X).app n σ ∈ X.core.obj n}
  map θ σ hσ a := by
    rw [NatTrans.naturality_apply]
    exact X.core.map θ (hσ a)

theorem core_le_objectwiseCore (A X : SSet.{u}) [X.Quasicategory] :
    ((ihom A).obj X).core ≤ objectwiseCore A X :=
  fun _ σ hσ a ↦ range_core_ι_comp_le_core (evalVertex a X) _ ⟨⟨σ, hσ⟩, rfl⟩

lemma range_le_objectwiseCore_iff_forall {A X Z : SSet.{u}} (g : Z ⟶ (ihom A).obj X) :
    Subcomplex.range g ≤ objectwiseCore A X ↔
      ∀ a : A _⦋0⦌, Subcomplex.range (g ≫ evalVertex a X) ≤ X.core :=
  ⟨fun h a n _ ⟨σ, hσ⟩ ↦ hσ ▸ h n ⟨σ, rfl⟩ a, fun h n _ ⟨σ, hσ⟩ a ↦ hσ ▸ h a n ⟨σ, rfl⟩⟩

end ObjectwiseCore

section Invertible

lemma ihom_terminal_hom_ext {K Z : SSet.{u}} (f g : Z ⟶ (ihom K).obj (⊤_ SSet.{u})) :
    f = g :=
  uncurry_injective (terminal.hom_ext _ _)

instance quasicategory_terminal : (⊤_ SSet.{u}).Quasicategory := by
  have : IsIso (terminal.from (⊤_ SSet.{u})) :=
    isIso_of_isTerminal terminalIsTerminal terminalIsTerminal _
  rw [quasicategory_iff_innerFibration]
  exact ⟨rlp_of_isIso _ _⟩

private noncomputable def terminalPullbackObjObj {K L : SSet.{u}} (v : K ⟶ L) (X : SSet.{u}) :
    MonoidalClosed.internalHom.PullbackObjObj v (terminal.from X) where
  pt := (ihom K).obj X
  fst := 𝟙 _
  snd := curry (terminal.from _)
  isPullback := by
    have : Mono ((MonoidalClosed.internalHom.map v.op).app (⊤_ SSet.{u})) :=
      ⟨fun _ _ _ ↦ ihom_terminal_hom_ext _ _⟩
    have : IsIso (𝟙 ((ihom K).obj X)) := inferInstance
    exact IsPullback.of_horiz_isIso_mono (fst := 𝟙 ((ihom K).obj X)) ⟨ihom_terminal_hom_ext _ _⟩
  π := (pre v).app X
  π_fst := Category.comp_id _
  π_snd := ihom_terminal_hom_ext _ _

private lemma hasLiftingProperty_boundary_pre_coherentIso_hom (X : SSet.{u}) [X.Quasicategory]
    (n : ℕ) :
    HasLiftingProperty (∂Δ[n + 1] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      ((pre (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u})).app X) :=
  (hasLiftingProperty_pullbackObjObjπ_comm _ _ (terminal.from X)
    (terminalPullbackObjObj _ X) _).2
    (hasLiftingProperty_coherentIso_hom_pullbackObjObjπ_succ (terminal.from X) n)

private theorem nonempty_invStruct_of_mem_objectwiseCore {A X : SSet.{u}} [X.Quasicategory]
    (e : ((ihom A).obj X) _⦋1⦌) (he : e ∈ (objectwiseCore A X).obj _) :
    Nonempty (Edge.mk' e).InvStruct := by
  let hom : Δ[1] ⟶ coherentIso.{u} := yonedaEquiv.symm coherentIso.hom.edge
  let g : A ⊗ Δ[1] ⟶ X := uncurry (yonedaEquiv.symm e)
  let w : A ⟶ (ihom Δ[1]).obj X := curry ((β_ Δ[1] A).hom ≫ g)
  have sq : CommSq (Subcomplex.isInitialBot.to _) (⊥ : A.Subcomplex).ι ((pre hom).app X) w :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  have h₀ (y : A _⦋0⦌) (_ : y ∉ Set.range ((⊥ : A.Subcomplex).ι.app _)) :
      ∃ x : Δ[0] ⟶ (ihom coherentIso.{u}).obj X,
        x ≫ (pre hom).app X = yonedaEquiv.symm y ≫ w := by
    let ey : Δ[1] ⟶ X := lift (stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm y) (𝟙 _) ≫ g
    have hey : yonedaEquiv ey ∈ X.core.obj _ := by
      have hey' : ey = yonedaEquiv.symm e ≫ evalVertex y X := (comp_evalVertex y _).symm
      rw [hey', yonedaEquiv_comp, Equiv.apply_symm_apply]
      exact he y
    obtain ⟨G, hG⟩ := exists_coherentIso_extension (Edge.mk' (yonedaEquiv ey))
      ((isIso_homMk_iff _).1 (isIso_homMk_of_mem_core _ hey)).some
    have hGe : hom ≫ G = ey := yonedaEquiv.injective (by
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← Edge.map_edge, hG]
      rfl)
    refine ⟨curry (fst _ _ ≫ G), ?_⟩
    rw [curry_pre_app, whiskerRight_fst_assoc, hGe, ← curry_natural_left]
    congr 1
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    ext1 <;> simp
  obtain ⟨l⟩ := (hasLift_of_mono _ (hasLiftingProperty_boundary_pre_coherentIso_hom X) sq
    h₀).exists_lift
  let G : coherentIso.{u} ⟶ (ihom A).obj X := curry ((β_ A coherentIso).hom ≫ uncurry l.l)
  have hG : hom ≫ G = yonedaEquiv.symm e := by
    rw [← curry_natural_left, BraidedCategory.braiding_naturality_right_assoc,
      ← uncurry_pre_app, l.fac_right, uncurry_curry, SymmetricCategory.symmetry_assoc,
      curry_uncurry]
  have he' : G.app _ coherentIso.hom.edge = e := by
    have := congrArg yonedaEquiv hG
    rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact he' ▸ coherentIso.nonempty_invStruct_app G _

theorem objectwiseCore_eq_core (A X : SSet.{u}) [X.Quasicategory] :
    objectwiseCore A X = ((ihom A).obj X).core := by
  refine le_antisymm ?_ (core_le_objectwiseCore A X)
  rintro ⟨⟨k⟩⟩ σ hσ
  refine mem_core_of_isIso (n := k) σ fun i _ ↦ ?_
  exact (nonempty_invStruct_of_mem_objectwiseCore _ ((objectwiseCore A X).map
    (SimplexCategory.mkOfLe 0 i (Fin.zero_le _)).op hσ)).some.isIso_homMk

theorem nonempty_invStruct_ihom_iff {A X : SSet.{u}} [X.Quasicategory]
    (e : ((ihom A).obj X) _⦋1⦌) :
    Nonempty (Edge.mk' e).InvStruct ↔ e ∈ (objectwiseCore A X).obj _ := by
  rw [objectwiseCore_eq_core]
  exact ⟨fun ⟨I⟩ ↦ edge_mem_core_of_isIso _ I.isIso_homMk,
    fun h ↦ (isIso_homMk_iff _).1 (isIso_homMk_of_mem_core _ h)⟩

instance kanComplex_objectwiseCore (A X : SSet.{u}) [X.Quasicategory] :
    (objectwiseCore A X : SSet.{u}).KanComplex := by
  rw [objectwiseCore_eq_core]
  infer_instance

end Invertible

section Restriction

noncomputable def objectwiseCoreMap (A : SSet.{u}) {X Y : SSet.{u}} [X.Quasicategory]
    (p : X ⟶ Y) : (objectwiseCore A X : SSet.{u}) ⟶ (objectwiseCore A Y : SSet.{u}) :=
  Subcomplex.lift ((objectwiseCore A X).ι ≫ (ihom A).map p) (by
    rintro n _ ⟨σ, rfl⟩ a
    have h := ConcreteCategory.congr_hom (congr_app (ihom_map_comp_evalVertex a p) n) σ.1
    exact h ▸ range_core_ι_comp_le_core p n ⟨⟨_, σ.2 a⟩, rfl⟩)

@[reassoc (attr := simp)]
lemma objectwiseCoreMap_ι (A : SSet.{u}) {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) :
    objectwiseCoreMap A p ≫ (objectwiseCore A Y).ι = (objectwiseCore A X).ι ≫ (ihom A).map p :=
  Subcomplex.lift_ι _ _

noncomputable def objectwiseCorePre {A B : SSet.{u}} (i : A ⟶ B) (X : SSet.{u}) :
    (objectwiseCore B X : SSet.{u}) ⟶ (objectwiseCore A X : SSet.{u}) :=
  Subcomplex.lift ((objectwiseCore B X).ι ≫ (pre i).app X) (by
    rintro n _ ⟨σ, rfl⟩ a
    have h := ConcreteCategory.congr_hom (congr_app (pre_app_comp_evalVertex (X := X) i a) n) σ.1
    exact h ▸ σ.2 (i.app _ a))

@[reassoc (attr := simp)]
lemma objectwiseCorePre_ι {A B : SSet.{u}} (i : A ⟶ B) (X : SSet.{u}) :
    objectwiseCorePre i X ≫ (objectwiseCore A X).ι = (objectwiseCore B X).ι ≫ (pre i).app X :=
  Subcomplex.lift_ι _ _

noncomputable def objectwiseCoreRestrict {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y)
    {A B : SSet.{u}} (i : A ⟶ B) :
    (objectwiseCore B X : SSet.{u}) ⟶
      pullback (objectwiseCoreMap A p) (objectwiseCorePre i Y) :=
  pullback.lift (objectwiseCorePre i X) (objectwiseCoreMap B p) (by
    rw [← cancel_mono (objectwiseCore A Y).ι, Category.assoc, Category.assoc, objectwiseCoreMap_ι,
      objectwiseCorePre_ι_assoc, objectwiseCorePre_ι, objectwiseCoreMap_ι_assoc,
      pre_comm_ihom_map])

@[reassoc (attr := simp)]
lemma objectwiseCoreRestrict_fst {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) {A B : SSet.{u}}
    (i : A ⟶ B) : objectwiseCoreRestrict p i ≫ pullback.fst _ _ = objectwiseCorePre i X :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma objectwiseCoreRestrict_snd {X Y : SSet.{u}} [X.Quasicategory] (p : X ⟶ Y) {A B : SSet.{u}}
    (i : A ⟶ B) : objectwiseCoreRestrict p i ≫ pullback.snd _ _ = objectwiseCoreMap B p :=
  pullback.lift_snd _ _ _

private lemma ihom_bot_hom_ext {A X Z : SSet.{u}}
    (f g : Z ⟶ (ihom ((⊥ : A.Subcomplex) : SSet.{u})).obj X) : f = g :=
  uncurry_injective (by
    ext n ⟨⟨a, ha⟩, _⟩
    exact ha.elim)

private noncomputable def botPullbackObjObj (A : SSet.{u}) {X Y : SSet.{u}} (p : X ⟶ Y) :
    MonoidalClosed.internalHom.PullbackObjObj (⊥ : A.Subcomplex).ι p where
  pt := (ihom A).obj Y
  fst := curry (fst _ _ ≫ Subcomplex.isInitialBot.to X)
  snd := 𝟙 _
  isPullback := by
    have : Mono ((MonoidalClosed.internalHom.obj (op ((⊥ : A.Subcomplex) : SSet.{u}))).map p) :=
      ⟨fun _ _ _ ↦ ihom_bot_hom_ext _ _⟩
    have : IsIso (𝟙 ((ihom A).obj Y)) := inferInstance
    exact IsPullback.of_vert_isIso_mono (snd := 𝟙 ((ihom A).obj Y)) ⟨ihom_bot_hom_ext _ _⟩
  π := (ihom A).map p
  π_fst := ihom_bot_hom_ext _ _
  π_snd := Category.comp_id _

instance isofibration_ihom_map (A : SSet.{u}) {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (p : X ⟶ Y) [Isofibration p] : Isofibration ((ihom A).map p) :=
  isofibration_pullbackObjObjπ p (⊥ : A.Subcomplex).ι (botPullbackObjObj A p)

theorem exists_coherentIso_lift {E B : SSet.{u}} [E.Quasicategory] [B.Quasicategory]
    (q : E ⟶ B) [Isofibration q] (f : Δ[1] ⟶ E)
    (hf : Nonempty (Edge.mk' (yonedaEquiv f)).InvStruct) (G : coherentIso.{u} ⟶ B)
    (h : yonedaEquiv.symm coherentIso.hom.edge ≫ G = f ≫ q) :
    ∃ F : coherentIso.{u} ⟶ E, yonedaEquiv.symm coherentIso.hom.edge ≫ F = f ∧ F ≫ q = G := by
  have := coherentIso.mono_hom_edge.{u}
  have hlift : HasLiftingProperty (yonedaEquiv.symm coherentIso.hom.edge : Δ[1] ⟶ coherentIso.{u})
      (coreMap q) :=
    hasLiftingProperty_of_range_ι _ _ (coherentIso.hasLiftingProperty_ι_of_horn_zero false 1 _
      coherentIso.mem_range_hom_iff _ (hasLiftingProperty_horn_zero_coreMap q))
  have hu : Subcomplex.range f ≤ E.core := by
    rw [Subcomplex.range_eq_ofSimplex, Subcomplex.ofSimplex_le_iff]
    exact edge_mem_core_of_isIso _ hf.some.isIso_homMk
  have hv : Subcomplex.range G ≤ B.core :=
    range_le_core G fun e ↦ coherentIso.nonempty_invStruct_app (𝟙 _) e
  have sq : CommSq (Subcomplex.lift f hu) (yonedaEquiv.symm coherentIso.hom.edge) (coreMap q)
      (Subcomplex.lift G hv) := ⟨by
    rw [← cancel_mono B.core.ι, Category.assoc, coreMap_ι, Subcomplex.lift_ι_assoc,
      Category.assoc, Subcomplex.lift_ι, h]⟩
  obtain ⟨l⟩ := (hlift.sq_hasLift sq).exists_lift
  exact ⟨l.l ≫ E.core.ι, by rw [← Category.assoc, l.fac_left, Subcomplex.lift_ι], by
    rw [Category.assoc, ← coreMap_ι, ← Category.assoc, l.fac_right, Subcomplex.lift_ι]⟩

private lemma range_le_core_pullbackObjObj {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (p : X ⟶ Y) [Isofibration p] {A B : SSet.{u}} (i : A ⟶ B)
    (sq₁₃ : MonoidalClosed.internalHom.PullbackObjObj i p)
    {c : pullback (objectwiseCoreMap A p) (objectwiseCorePre i Y) ⟶ sq₁₃.pt}
    (hc₁ : c ≫ sq₁₃.fst = pullback.fst _ _ ≫ (objectwiseCore A X).ι)
    (hc₂ : c ≫ sq₁₃.snd = pullback.snd _ _ ≫ (objectwiseCore B Y).ι) :
    Subcomplex.range c ≤ sq₁₃.pt.core := by
  have hedge (z : (pullback (objectwiseCoreMap A p) (objectwiseCorePre i Y)) _⦋1⦌) :
      Nonempty (Edge.mk' (c.app _ z)).InvStruct := by
    let hom : Δ[1] ⟶ coherentIso.{u} := yonedaEquiv.symm coherentIso.hom.edge
    let ζ := yonedaEquiv.symm z
    have hge : yonedaEquiv (ζ ≫ pullback.snd _ _ ≫ (objectwiseCore B Y).ι) =
        ((pullback.snd (objectwiseCoreMap A p) (objectwiseCorePre i Y)).app _ z).1 := by
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rfl
    have hfe : yonedaEquiv (ζ ≫ pullback.fst _ _ ≫ (objectwiseCore A X).ι) =
        ((pullback.fst (objectwiseCoreMap A p) (objectwiseCorePre i Y)).app _ z).1 := by
      rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
      rfl
    have hg := (nonempty_invStruct_ihom_iff _).2
      (Subtype.property ((pullback.snd (objectwiseCoreMap A p) (objectwiseCorePre i Y)).app _ z))
    have hf := (nonempty_invStruct_ihom_iff _).2
      (Subtype.property ((pullback.fst (objectwiseCoreMap A p) (objectwiseCorePre i Y)).app _ z))
    rw [← hge] at hg
    rw [← hfe] at hf
    obtain ⟨G, hG⟩ := exists_coherentIso_extension _ hg.some
    have hGe : hom ≫ G = ζ ≫ pullback.snd _ _ ≫ (objectwiseCore B Y).ι :=
      yonedaEquiv.injective (by
        rw [yonedaEquiv_comp, Equiv.apply_symm_apply, ← Edge.map_edge, hG]
        rfl)
    obtain ⟨F, hF₁, hF₂⟩ := exists_coherentIso_lift ((ihom A).map p) _ hf
      (G ≫ (pre i).app Y) (by
        rw [← Category.assoc, hGe, Category.assoc, Category.assoc, ← objectwiseCorePre_ι,
          ← pullback.condition_assoc, objectwiseCoreMap_ι]
        simp only [Category.assoc])
    let H := sq₁₃.isPullback.lift F G hF₂
    have hH₁ : H ≫ sq₁₃.fst = F := sq₁₃.isPullback.lift_fst _ _ _
    have hH₂ : H ≫ sq₁₃.snd = G := sq₁₃.isPullback.lift_snd _ _ _
    have hH : hom ≫ H = ζ ≫ c := sq₁₃.isPullback.hom_ext
      (by rw [Category.assoc, hH₁, Category.assoc, hc₁]; exact hF₁)
      (by rw [Category.assoc, hH₂, Category.assoc, hc₂]; exact hGe)
    have he : H.app _ coherentIso.hom.edge = c.app _ z := by
      have := congrArg yonedaEquiv hH
      rwa [yonedaEquiv_comp, Equiv.apply_symm_apply, yonedaEquiv_comp,
        Equiv.apply_symm_apply] at this
    exact he ▸ coherentIso.nonempty_invStruct_app H _
  rintro ⟨⟨k⟩⟩ _ ⟨σ, rfl⟩
  refine mem_core_of_isIso (n := k) _ fun j _ ↦ ?_
  rw [← NatTrans.naturality_apply]
  exact (hedge _).some.isIso_homMk

theorem kanFibration_objectwiseCore_restrict {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (p : X ⟶ Y) [Isofibration p] {A B : SSet.{u}} (i : A ⟶ B) [Mono i] :
    modelCategoryQuillen.J.rlp (objectwiseCoreRestrict p i) := by
  intro K L f hf
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p
  let π : (ihom B).obj X ⟶ sq₁₃.pt := sq₁₃.π
  have := quasicategory_pullbackObjObj_pt p i sq₁₃
  have : Isofibration π := isofibration_pullbackObjObjπ p i sq₁₃
  have hk : HasLiftingProperty f (coreMap π) := kanFibration_coreMap π _ hf
  have key : (pullback.fst (objectwiseCoreMap A p) (objectwiseCorePre i Y) ≫
      (objectwiseCore A X).ι) ≫ (ihom A).map p =
        (pullback.snd (objectwiseCoreMap A p) (objectwiseCorePre i Y) ≫
          (objectwiseCore B Y).ι) ≫ (pre i).app Y := by
    rw [Category.assoc, ← objectwiseCoreMap_ι, pullback.condition_assoc,
      objectwiseCorePre_ι, Category.assoc]
  let c : pullback (objectwiseCoreMap A p) (objectwiseCorePre i Y) ⟶ sq₁₃.pt :=
    sq₁₃.isPullback.lift _ _ key
  have hc₁ : c ≫ sq₁₃.fst = pullback.fst _ _ ≫ (objectwiseCore A X).ι :=
    sq₁₃.isPullback.lift_fst _ _ _
  have hc₂ : c ≫ sq₁₃.snd = pullback.snd _ _ ≫ (objectwiseCore B Y).ι :=
    sq₁₃.isPullback.lift_snd _ _ _
  have hc : Subcomplex.range c ≤ sq₁₃.pt.core := range_le_core_pullbackObjObj p i sq₁₃ hc₁ hc₂
  have hcm {Z : SSet.{u}} (g h : Z ⟶ pullback (objectwiseCoreMap A p) (objectwiseCorePre i Y))
      (hgh : g ≫ c = h ≫ c) : g = h := by
    have h₁ := congrArg (· ≫ sq₁₃.fst) hgh
    have h₂ := congrArg (· ≫ sq₁₃.snd) hgh
    simp only [Category.assoc, hc₁, hc₂] at h₁ h₂
    refine pullback.hom_ext ?_ ?_
    · rw [← cancel_mono (objectwiseCore A X).ι, Category.assoc, Category.assoc]
      exact h₁
    · rw [← cancel_mono (objectwiseCore B Y).ι, Category.assoc, Category.assoc]
      exact h₂
  have e₁ : objectwiseCoreRestrict p i ≫ pullback.fst _ _ ≫ (objectwiseCore A X).ι =
      (objectwiseCore B X).ι ≫ (pre i).app X := by
    rw [objectwiseCoreRestrict, pullback.lift_fst_assoc, objectwiseCorePre_ι]
  have e₂ : objectwiseCoreRestrict p i ≫ pullback.snd _ _ ≫ (objectwiseCore B Y).ι =
      (objectwiseCore B X).ι ≫ (ihom B).map p := by
    rw [objectwiseCoreRestrict, pullback.lift_snd_assoc, objectwiseCoreMap_ι]
  have hr : objectwiseCoreRestrict p i ≫ c = (objectwiseCore B X).ι ≫ π :=
    sq₁₃.isPullback.hom_ext
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hc₁).trans (e₁.trans
        ((congrArg (_ ≫ ·) sq₁₃.π_fst).symm.trans (Category.assoc _ _ _).symm))))
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hc₂).trans (e₂.trans
        ((congrArg (_ ≫ ·) sq₁₃.π_snd).symm.trans (Category.assoc _ _ _).symm))))
  refine ⟨fun {a b} sq ↦ ?_⟩
  have hb : Subcomplex.range (b ≫ c) ≤ sq₁₃.pt.core := by
    rintro n _ ⟨x, rfl⟩
    exact hc n ⟨_, rfl⟩
  have sq' : CommSq (a ≫ Subcomplex.homOfLE (objectwiseCore_eq_core B X).le) f
      (coreMap π) (Subcomplex.lift _ hb) := ⟨by
    rw [← cancel_mono sq₁₃.pt.core.ι, Category.assoc, coreMap_ι, Category.assoc,
      Subcomplex.homOfLE_ι_assoc, ← hr, ← Category.assoc, sq.w, Category.assoc,
      Category.assoc, Subcomplex.lift_ι]⟩
  obtain ⟨l⟩ := (hk.sq_hasLift sq').exists_lift
  refine ⟨⟨⟨l.l ≫ Subcomplex.homOfLE (objectwiseCore_eq_core B X).ge, ?_, hcm _ _ ?_⟩⟩⟩
  · rw [← cancel_mono (objectwiseCore B X).ι]
    simp only [Category.assoc, Subcomplex.homOfLE_ι]
    rw [← Category.assoc, l.fac_left, Category.assoc, Subcomplex.homOfLE_ι]
  · simp only [Category.assoc]
    rw [hr, Subcomplex.homOfLE_ι_assoc, ← coreMap_ι, ← Category.assoc, l.fac_right,
      Subcomplex.lift_ι]

end Restriction

end SSet
