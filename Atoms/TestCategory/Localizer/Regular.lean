import Atoms.ForMathlib.CategoryTheory.Adjunction.Evaluation
import Atoms.ForMathlib.CategoryTheory.Limits.FunctorToTypes
import Atoms.Homotopical.HomotopyColimit.ProjectiveCofibration
import Atoms.TestCategory.Presheaf.ElementsColimit
import Atoms.TestCategory.BasicLocalizer.GrothendieckConstruction

open CategoryTheory Limits MorphismProperty Opposite Atoms.Homotopical

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) {A : Type u} [SmallCategory A]

section Projective

theorem exists_lift_evaluation_of_projectiveCofibrations {I : Type u} [SmallCategory I]
    {F : I ⥤ Aᵒᵖ ⥤ Type u} (hF : projectiveCofibrations A I (initial.to F)) (a : A)
    {H K : I ⥤ Type u} (p : H ⟶ K) (hp : ∀ i, Function.Surjective (p.app i))
    (g : F ⋙ (evaluation Aᵒᵖ (Type u)).obj (op a) ⟶ K) :
    ∃ l : F ⋙ (evaluation Aᵒᵖ (Type u)).obj (op a) ⟶ H, l ≫ p = g := by
  let adj := evaluationAdjunctionLeft (Type u) (op a)
  let R := evaluationRightAdjoint (Type u) (op a)
  let g' : F ⟶ K ⋙ R :=
    { app := fun i => adj.homEquiv _ _ (g.app i)
      naturality := fun i j k => by
        change F.map k ≫ adj.homEquiv _ _ (g.app j) =
          adj.homEquiv _ _ (g.app i) ≫ R.map (K.map k)
        rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
        exact congrArg _ (g.naturality k) }
  obtain ⟨l', -, hl'⟩ := exists_lift_of_projectiveCofibrations hF
    (p := Functor.whiskerRight p R)
    (fun i => rlp_monomorphisms_evaluationRightAdjoint_map a (hp i))
    (initial.to _) g' (initial.hom_ext _ _)
  refine ⟨{ app := fun i => (adj.homEquiv _ _).symm (l'.app i), naturality := ?_ }, ?_⟩
  · intro i j k
    change ((evaluation Aᵒᵖ (Type u)).obj (op a)).map (F.map k) ≫
        (adj.homEquiv _ _).symm (l'.app j) = (adj.homEquiv _ _).symm (l'.app i) ≫ H.map k
    rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
    exact congrArg _ (l'.naturality k)
  · refine NatTrans.ext (funext fun i => ?_)
    change (adj.homEquiv _ _).symm (l'.app i) ≫ p.app i = g.app i
    rw [← adj.homEquiv_naturality_right_symm]
    have e : l'.app i ≫ R.map (p.app i) = g'.app i := congrArg (fun t => t.app i) hl'
    rw [e]
    exact (adj.homEquiv _ _).symm_apply_apply _

end Projective

section Fibre

variable {I : Type u} [SmallCategory I]

private theorem eqToHom_comp_snd_eq_of_eq_map {G : I ⥤ Type u} {j j' : I} (k : j ⟶ j')
    {e : Σ i, G.obj i} (p : G.FreeOnElementsObj j) (p' : G.FreeOnElementsObj j')
    (hp : p' = G.freeOnElements.map k p) (h : e.1 = p.1.1) (h' : e.1 = p'.1.1) :
    eqToHom h' ≫ p'.2 = (eqToHom h ≫ p.2) ≫ k := by
  subst hp
  exact (Category.assoc _ _ _).symm

private theorem map_eqToHom_comp_snd {G : I ⥤ Type u} {j : I} {e : Σ i, G.obj i}
    (p : G.FreeOnElementsObj j) (he : e = p.1) (h : e.1 = p.1.1) :
    G.map (eqToHom h ≫ p.2) e.2 = G.map p.2 p.1.2 := by
  obtain ⟨e', f⟩ := p
  subst he
  simp

theorem fst_eq_of_colimitFiberFunctor (F : I ⥤ Aᵒᵖ ⥤ Type u) (a : A)
    (s : (colimit F).obj (op a))
    (σ : F ⋙ (evaluation Aᵒᵖ (Type u)).obj (op a) ⟶
      (F ⋙ (evaluation Aᵒᵖ (Type u)).obj (op a)).freeOnElements)
    {j j' : I} (x : (colimitFiberFunctor A F (colimit.cocone F) a s).obj j)
    (x' : (colimitFiberFunctor A F (colimit.cocone F) a s).obj j') :
    (σ.app j x.1).1 = (σ.app j' x'.1).1 := by
  let G := F ⋙ (evaluation Aᵒᵖ (Type u)).obj (op a)
  have hc := isColimitOfPreserves ((evaluation Aᵒᵖ (Type u)).obj (op a)) (colimit.isColimit F)
  let c : Cocone G :=
    { pt := Σ i, G.obj i
      ι :=
        { app := fun i => ↾fun y => (σ.app i y).1
          naturality := fun i i' k => ConcreteCategory.hom_ext _ _ fun y =>
            congrArg Sigma.fst (NatTrans.naturality_apply σ k y) } }
  have fac : ∀ i (y : G.obj i), hc.desc c ((colimit.ι F i).app (op a) y) = (σ.app i y).1 :=
    fun i y => ConcreteCategory.congr_hom (hc.fac c i) y
  exact (fac j x.1).symm.trans ((congrArg (hc.desc c) x.2).trans
    ((congrArg (hc.desc c) x'.2).symm.trans (fac j' x'.1)))

theorem exists_retract_coyoneda_colimitFiberFunctor (F : I ⥤ Aᵒᵖ ⥤ Type u)
    (hF : projectiveCofibrations A I (initial.to F)) (a : A) (s : (colimit F).obj (op a)) :
    ∃ i₁ : I, Nonempty
      (Retract (colimitFiberFunctor A F (colimit.cocone F) a s) (coyoneda.obj (op i₁))) := by
  let G := F ⋙ (evaluation Aᵒᵖ (Type u)).obj (op a)
  let C := colimitFiberFunctor A F (colimit.cocone F) a s
  obtain ⟨σ, hσ⟩ := exists_lift_evaluation_of_projectiveCofibrations hF a G.freeOnElementsπ
    G.freeOnElementsπ_surjective (𝟙 G)
  have hπ : ∀ j (y : G.obj j), G.map (σ.app j y).2 (σ.app j y).1.2 = y := fun j y =>
    ConcreteCategory.congr_hom (congrArg (fun t : G ⟶ G => t.app j) hσ) y
  have hc := isColimitOfPreserves ((evaluation Aᵒᵖ (Type u)).obj (op a)) (colimit.isColimit F)
  obtain ⟨j₀, y₀, hy₀⟩ := Types.jointly_surjective_of_isColimit hc s
  let x₀ : C.obj j₀ := ⟨y₀, hy₀⟩
  let e₀ := (σ.app j₀ y₀).1
  have he₀ : (colimit.ι F e₀.1).app (op a) e₀.2 = s :=
    (FunctorToTypes.colimit_ι_app_map_apply F a (σ.app j₀ y₀).2 e₀.2).symm.trans
      ((congrArg ((colimit.ι F j₀).app (op a)) (hπ j₀ y₀)).trans hy₀)
  have hfst : ∀ {j} (x : C.obj j), e₀.1 = (σ.app j x.1).1.1 := fun x =>
    congrArg Sigma.fst (fst_eq_of_colimitFiberFunctor F a s σ x₀ x)
  let ι : C ⟶ coyoneda.obj (op e₀.1) :=
    { app := fun j => ↾fun x => eqToHom (hfst x) ≫ (σ.app j x.1).2
      naturality := fun j j' k => ConcreteCategory.hom_ext _ _ fun x =>
        eqToHom_comp_snd_eq_of_eq_map k (σ.app j x.1) (σ.app j' (C.map k x).1)
          (NatTrans.naturality_apply σ k x.1) (hfst x) (hfst (C.map k x)) }
  let ρ : coyoneda.obj (op e₀.1) ⟶ C :=
    { app := fun j => ↾fun f =>
        (⟨(F.map f).app (op a) e₀.2,
          (FunctorToTypes.colimit_ι_app_map_apply F a f e₀.2).trans he₀⟩ : C.obj j)
      naturality := fun j j' k => ConcreteCategory.hom_ext _ _ fun f =>
        Subtype.ext (Functor.map_comp_apply G f k e₀.2) }
  refine ⟨e₀.1, ⟨{ i := ι, r := ρ, retract := ?_ }⟩⟩
  refine NatTrans.ext (funext fun j => ConcreteCategory.hom_ext _ _ fun x => Subtype.ext ?_)
  exact (map_eqToHom_comp_snd (σ.app j x.1)
    (fst_eq_of_colimitFiberFunctor F a s σ x₀ x) (hfst x)).trans (hπ j x.1)

namespace BasicLocalizer

theorem aspherical_colimitFiberFunctor_elements_of_projectiveCofibrations {I : Type u}
    [SmallCategory I] (F : I ⥤ Aᵒᵖ ⥤ Type u)
    (hF : projectiveCofibrations A I (initial.to F)) (a : A)
    (s : (colimit F).obj (Opposite.op a)) :
    𝒲.Aspherical (Cat.of (colimitFiberFunctor A F (colimit.cocone F) a s).Elements) := by
  obtain ⟨i₁, ⟨r⟩⟩ := exists_retract_coyoneda_colimitFiberFunctor F hF a s
  let r' := r.map Functor.elementsFunctor
  have hR := @BasicLocalizer.aspherical_of_hasInitial 𝒲
    (Cat.of (coyoneda.obj (op i₁)).Elements)
    (Functor.Elements.isInitialOfCorepresentableBy
      (Functor.CorepresentableBy.coyoneda (op i₁))).hasInitial
  let R : RetractArrow
      (terminal.from (Cat.of (colimitFiberFunctor A F (colimit.cocone F) a s).Elements))
      (terminal.from (Cat.of (coyoneda.obj (op i₁)).Elements)) :=
    { i := Arrow.homMk r'.i (𝟙 _) (terminal.hom_ext _ _)
      r := Arrow.homMk r'.r (𝟙 _) (terminal.hom_ext _ _)
      retract := Arrow.hom_ext _ _ r'.retract (terminal.hom_ext _ _) }
  exact 𝒲.W.of_retract R hR

end BasicLocalizer

theorem hasInitial_colimitFiberFunctor_representablesOver (X : Aᵒᵖ ⥤ Type u) (a : A)
    (s : X.obj (Opposite.op a)) :
    HasInitial (colimitFiberFunctor A (representablesOver X) (Presheaf.tautologicalCocone X) a
      s).Elements := by
  let C := colimitFiberFunctor A (representablesOver X) (Presheaf.tautologicalCocone X) a s
  let p₀ : C.Elements :=
    ⟨CostructuredArrow.mk (yonedaEquiv.symm s), ⟨𝟙 a, yonedaEquiv.apply_symm_apply s⟩⟩
  let hom : ∀ p : C.Elements, p₀ ⟶ p := fun p =>
    ⟨CostructuredArrow.homMk p.2.1 (yonedaEquiv.injective ((yonedaEquiv_comp _ _).trans
        ((congrArg (fun y => p.1.hom.app (op a) y) (yonedaEquiv_yoneda_map p.2.1)).trans
          (p.2.2.trans (yonedaEquiv.apply_symm_apply s).symm)))),
      Subtype.ext (Category.id_comp p.2.1)⟩
  refine IsInitial.hasInitial (IsInitial.ofUniqueHom hom fun p m => ?_)
  refine CategoryOfElements.ext _ _ _ (CostructuredArrow.hom_ext _ _ ?_)
  exact (Category.id_comp _).symm.trans (congrArg Subtype.val m.2)

namespace BasicLocalizer

theorem isRegularALocalizer_wPsh
    (h : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u)).rlp ≤ 𝒲.wPsh A) :
    IsRegularALocalizer (𝒲.wPsh A) := by
  refine ⟨fun X => ?_⟩
  let Q := (projectiveReplacement A (CostructuredArrow yoneda X)).obj (representablesOver X)
  let π : Q ⟶ representablesOver X :=
    (projectiveReplacementπ A (CostructuredArrow yoneda X)).app (representablesOver X)
  have hf : ∀ i, (colimit.cocone Q).ι.app i ≫ regularizationMap X =
      π.app i ≫ (Presheaf.tautologicalCocone X).ι.app i := fun i => by
    change colimit.ι Q i ≫ colimMap π ≫
      colimit.desc (representablesOver X) (Presheaf.tautologicalCocone X) = _
    rw [ι_colimMap_assoc, colimit.ι_desc]
  have sq := elementsColimitComparison_naturality A π (colimit.cocone Q)
    (Presheaf.tautologicalCocone X) (regularizationMap X) hf
  have hG : 𝒲.W (Grothendieck.map (Functor.whiskerRight π (elementsFunctor A))).toCatHom :=
    𝒲.W_grothendieckMap _ fun i => h _ (rlp_monomorphisms_projectiveReplacementπ_app _ i)
  have hφ : 𝒲.W (elementsColimitComparison A _ (Presheaf.tautologicalCocone X)) :=
    𝒲.W_elementsColimitComparison A _ _ fun a s =>
      @BasicLocalizer.aspherical_of_hasInitial 𝒲 (Cat.of _)
        (hasInitial_colimitFiberFunctor_representablesOver X a s)
  have hQ : 𝒲.W (elementsColimitComparison A Q (colimit.cocone Q)) :=
    𝒲.W_elementsColimitComparison A _ _ fun a s =>
      𝒲.aspherical_colimitFiberFunctor_elements_of_projectiveCofibrations Q
        (projectiveCofibrations_initial_to_projectiveReplacement _) a s
  have hcomp : 𝒲.W (elementsColimitComparison A Q (colimit.cocone Q) ≫
      (elementsFunctor A).map (regularizationMap X)) :=
    (congrArg (fun f => 𝒲.W f) sq).mp (𝒲.W.comp_mem _ _ hG hφ)
  exact 𝒲.W.of_precomp _ _ hQ hcomp

end BasicLocalizer

end Fibre

end Atoms.TestCategory
