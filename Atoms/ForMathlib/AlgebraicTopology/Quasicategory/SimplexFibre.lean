import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.InvertingHom
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FibrewisePath
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Spine

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed CartesianMonoidalCategory
  HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

section Fibre

variable {K L : SSet.{u}} {n : ℕ}

noncomputable def ihomEvalVertices (v : Fin (n + 1) → K _⦋0⦌) (X : SSet.{u}) :
    (ihom K).obj X ⟶ ∏ᶜ fun _ : Fin (n + 1) ↦ X :=
  Pi.lift fun i ↦ evalVertex (v i) X

@[reassoc (attr := simp)]
lemma ihomEvalVertices_π (v : Fin (n + 1) → K _⦋0⦌) (X : SSet.{u}) (i : Fin (n + 1)) :
    ihomEvalVertices v X ≫ Pi.π _ i = evalVertex (v i) X :=
  Pi.lift_π _ _

noncomputable def ihomFibre (v : Fin (n + 1) → K _⦋0⦌) (X : SSet.{u})
    (x : Fin (n + 1) → X _⦋0⦌) : SSet.{u} :=
  pullback (ihomEvalVertices v X) (Pi.lift fun i ↦ yonedaEquiv.symm (x i))

namespace ihomFibre

variable (v : Fin (n + 1) → K _⦋0⦌) (X : SSet.{u}) (x : Fin (n + 1) → X _⦋0⦌)

noncomputable def ι : ihomFibre v X x ⟶ (ihom K).obj X :=
  pullback.fst _ _

@[reassoc (attr := simp)]
lemma ι_evalVertex (i : Fin (n + 1)) : ι v X x ≫ evalVertex (v i) X = const (x i) := by
  have h := pullback.condition (f := ihomEvalVertices v X)
    (g := Pi.lift fun i ↦ yonedaEquiv.symm (x i)) =≫ Pi.π _ i
  simp only [Category.assoc, ihomEvalVertices_π, Pi.lift_π, yonedaEquiv_symm_zero,
    comp_const] at h
  exact h

instance : Mono (ι v X x) :=
  have : Mono (Pi.lift fun i ↦ yonedaEquiv.symm (x i) : Δ[0] ⟶ ∏ᶜ fun _ : Fin (n + 1) ↦ X) :=
    stdSimplex.isTerminalObj₀.mono_from _
  inferInstanceAs (Mono (pullback.fst _ _))

variable {v X x}

noncomputable def lift {T : SSet.{u}} (a : T ⟶ (ihom K).obj X)
    (ha : ∀ i, a ≫ evalVertex (v i) X = const (x i)) : T ⟶ ihomFibre v X x :=
  pullback.lift a (stdSimplex.isTerminalObj₀.from T) (Pi.hom_ext _ _ fun i ↦ by
    simp only [Category.assoc, ihomEvalVertices_π, Pi.lift_π, ha, yonedaEquiv_symm_zero,
      comp_const])

@[reassoc (attr := simp)]
lemma lift_ι {T : SSet.{u}} (a : T ⟶ (ihom K).obj X)
    (ha : ∀ i, a ≫ evalVertex (v i) X = const (x i)) : lift a ha ≫ ι v X x = a :=
  pullback.lift_fst _ _ _

@[ext]
lemma hom_ext {T : SSet.{u}} {f g : T ⟶ ihomFibre v X x} (h : f ≫ ι v X x = g ≫ ι v X x) :
    f = g :=
  (cancel_mono _).1 h

noncomputable def map (i : K ⟶ L) {m : ℕ} {v : Fin (m + 1) → K _⦋0⦌} {w : Fin (n + 1) → L _⦋0⦌}
    (φ : Fin (m + 1) → Fin (n + 1)) (hφ : ∀ j, i.app _ (v j) = w (φ j)) (X : SSet.{u})
    (x : Fin (n + 1) → X _⦋0⦌) : ihomFibre w X x ⟶ ihomFibre v X (x ∘ φ) :=
  lift (ι w X x ≫ (pre i).app X) fun j ↦ by
    rw [Category.assoc, pre_app_comp_evalVertex, hφ, ι_evalVertex, Function.comp_apply]

@[reassoc (attr := simp)]
lemma map_ι (i : K ⟶ L) {m : ℕ} {v : Fin (m + 1) → K _⦋0⦌} {w : Fin (n + 1) → L _⦋0⦌}
    (φ : Fin (m + 1) → Fin (n + 1)) (hφ : ∀ j, i.app _ (v j) = w (φ j)) (X : SSet.{u})
    (x : Fin (n + 1) → X _⦋0⦌) :
    map i φ hφ X x ≫ ι v X (x ∘ φ) = ι w X x ≫ (pre i).app X :=
  lift_ι _ _

theorem isPullback_map (i : K ⟶ L) (v : Fin (n + 1) → K _⦋0⦌) (w : Fin (n + 1) → L _⦋0⦌)
    (hw : ∀ j, i.app _ (v j) = w j) (X : SSet.{u}) (x : Fin (n + 1) → X _⦋0⦌) :
    IsPullback (ι w X x) (map i id hw X x) ((pre i).app X) (ι v X x) := by
  have hev : (pre i).app X ≫ ihomEvalVertices v X = ihomEvalVertices w X :=
    Pi.hom_ext _ _ fun j ↦ by
      rw [Category.assoc, ihomEvalVertices_π, ihomEvalVertices_π, pre_app_comp_evalVertex, hw]
  have hsnd : map i id hw X x ≫ (pullback.snd _ _ : ihomFibre v X x ⟶ Δ[0]) =
      pullback.snd _ _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  have key : ∀ (f : (ihom L).obj X ⟶ ∏ᶜ fun _ : Fin (n + 1) ↦ X) (s : ihomFibre w X x ⟶ Δ[0]),
      f = ihomEvalVertices w X → s = pullback.snd _ _ →
        IsPullback (ι w X x) s f (Pi.lift fun i ↦ yonedaEquiv.symm (x i)) := by
    rintro _ _ rfl rfl
    exact IsPullback.of_hasPullback _ _
  exact IsPullback.of_bot (v₂₁ := pullback.snd _ _) (v₂₂ := ihomEvalVertices v X)
    (key _ _ hev hsnd) (map_ι i id hw X x).symm (IsPullback.of_hasPullback _ _)

end ihomFibre

noncomputable def isTerminalIhomFibreOfIsTerminal {K : SSet.{u}} (hK : IsTerminal K)
    (v : Fin 1 → K _⦋0⦌) (X : SSet.{u}) (x : Fin 1 → X _⦋0⦌) :
    IsTerminal (ihomFibre v X x) := by
  apply IsTerminal.ofUniqueHom
    (fun T => ihomFibre.lift (const (x 0) ≫ constDiagram K X) (fun i => by
      obtain rfl : i = 0 := Fin.eq_zero i
      rw [Category.assoc, constDiagram_comp_evalVertex, Category.comp_id]))
  intro T f
  apply ihomFibre.hom_ext
  apply uncurry_injective
  let s : T ⟶ K ⊗ T := lift (stdSimplex.isTerminalObj₀.from T ≫ yonedaEquiv.symm (v 0)) (𝟙 T)
  have : IsIso s := by
    refine ⟨⟨snd K T, lift_snd _ _, ?_⟩⟩
    apply CartesianMonoidalCategory.hom_ext
    · exact hK.hom_ext _ _
    · dsimp only [s]
      rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  apply (cancel_epi s).1
  rw [← comp_evalVertex, ← comp_evalVertex, Category.assoc, ihomFibre.ι_evalVertex,
    ihomFibre.lift_ι, Category.assoc, constDiagram_comp_evalVertex, Category.comp_id,
    comp_const]

theorem rlp_I_pre_app_of_innerAnodyneExtensions {i : K ⟶ L} (hi : innerAnodyneExtensions i)
    (X : SSet.{u}) [X.Quasicategory] : modelCategoryQuillen.I.rlp ((pre i).app X) :=
  fun _ _ _ ⟨k⟩ ↦ (internalHomAdjunction₂.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i ∂Δ[k].ι)
    (Functor.PullbackObjObj.ofIsTerminal MonoidalClosed.internalHom i (terminal.from X)
      terminalIsTerminal)).1
    (innerAnodyneExtensions_pushoutObjObjι' _ hi _ (mem_innerFibrations (terminal.from X)))

end Fibre

section SimplexFibre

variable (X : SSet.{u})

noncomputable abbrev simplexFibre {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) : SSet.{u} :=
  ihomFibre stdSimplex.obj₀Equiv.symm X x

noncomputable def simplexFibreMap {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (x : Fin (n + 1) → X _⦋0⦌) :
    simplexFibre X x ⟶ simplexFibre X (x ∘ f.toOrderHom) :=
  ihomFibre.map (stdSimplex.map f) f.toOrderHom (fun _ ↦ rfl) X x

@[reassoc (attr := simp)]
lemma simplexFibreMap_ι {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (x : Fin (n + 1) → X _⦋0⦌) :
    simplexFibreMap X f x ≫ ihomFibre.ι _ X _ =
      ihomFibre.ι _ X x ≫ (pre (stdSimplex.map f)).app X :=
  ihomFibre.map_ι _ _ _ _ _

@[simp]
theorem simplexFibreMap_id {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) :
    simplexFibreMap X (𝟙 ⦋n⦌) x = 𝟙 _ := by
  ext1
  rw [simplexFibreMap_ι, CategoryTheory.Functor.map_id stdSimplex, pre_id, NatTrans.id_app,
    Category.comp_id]
  exact (Category.id_comp _).symm

@[reassoc]
theorem simplexFibreMap_comp {l m n : ℕ} (f : ⦋l⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋n⦌)
    (x : Fin (n + 1) → X _⦋0⦌) :
    simplexFibreMap X (f ≫ g) x = simplexFibreMap X g x ≫ simplexFibreMap X f _ := by
  ext1
  have h₁ := simplexFibreMap_ι X (f ≫ g) x
  have h₂ : (simplexFibreMap X g x ≫ simplexFibreMap X f _) ≫ ihomFibre.ι _ X _ =
      ihomFibre.ι _ X x ≫ (pre (stdSimplex.map g)).app X ≫ (pre (stdSimplex.map f)).app X := by
    rw [Category.assoc, simplexFibreMap_ι, simplexFibreMap_ι_assoc]
  rw [CategoryTheory.Functor.map_comp stdSimplex, pre_map, NatTrans.comp_app] at h₁
  exact h₁.trans h₂.symm

noncomputable def simplexFibreOneIso (x : Fin 2 → X _⦋0⦌) :
    simplexFibre X x ≅ mappingSpace X (x 0) (x 1) where
  hom := pullback.lift (ihomFibre.ι _ X x) (stdSimplex.isTerminalObj₀.from _) (by
    rw [comp_ihomStdSimplexOneEval, ihomFibre.ι_evalVertex, ihomFibre.ι_evalVertex, comp_lift,
      yonedaEquiv_symm_zero, yonedaEquiv_symm_zero, comp_const, comp_const])
  inv := ihomFibre.lift (pullback.fst _ _) fun i ↦ by
    fin_cases i
    · exact (mappingSpace_fst_evalVertex_zero X _ _).trans
        ((congrArg (_ ≫ ·) (yonedaEquiv_symm_zero _)).trans (comp_const _ _))
    · exact (mappingSpace_fst_evalVertex_one X _ _).trans
        ((congrArg (_ ≫ ·) (yonedaEquiv_symm_zero _)).trans (comp_const _ _))
  hom_inv_id := ihomFibre.hom_ext ((Category.assoc _ _ _).trans
    ((congrArg _ (ihomFibre.lift_ι _ _)).trans
      ((pullback.lift_fst _ _ _).trans (Category.id_comp _).symm)))
  inv_hom_id := pullback.hom_ext ((Category.assoc _ _ _).trans
    ((congrArg _ (pullback.lift_fst _ _ _)).trans
      ((ihomFibre.lift_ι _ _).trans (Category.id_comp _).symm)))
    (stdSimplex.isTerminalObj₀.hom_ext _ _)

@[simp]
lemma simplexFibreOneIso_hom_fst (x : Fin 2 → X _⦋0⦌) :
    (simplexFibreOneIso X x).hom ≫ pullback.fst _ _ = ihomFibre.ι _ X x :=
  pullback.lift_fst _ _ _

noncomputable def simplexFibreEdge {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) (i j : Fin (n + 1))
    (hij : i ≤ j) : simplexFibre X x ⟶ mappingSpace X (x i) (x j) :=
  simplexFibreMap X (SimplexCategory.mkOfLe i j hij) x ≫ (simplexFibreOneIso X _).hom

lemma simplexFibreEdge_eq_simplexFibreMap {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) (i j : Fin (n + 1))
    (hij : i ≤ j) :
    simplexFibreEdge X x i j hij =
      simplexFibreMap X (SimplexCategory.mkOfLe i j hij) x ≫ (simplexFibreOneIso X _).hom :=
  rfl

@[reassoc]
lemma simplexFibreEdge_fst {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) (i j : Fin (n + 1))
    (hij : i ≤ j) :
    simplexFibreEdge X x i j hij ≫ pullback.fst _ _ =
      ihomFibre.ι _ X x ≫ (pre (stdSimplex.map (SimplexCategory.mkOfLe i j hij))).app X :=
  (Category.assoc _ _ _).trans ((congrArg _ (simplexFibreOneIso_hom_fst X _)).trans
    (simplexFibreMap_ι X _ x))

@[reassoc]
theorem simplexFibreMap_comp_simplexFibreEdge {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : Fin (n + 1) → X _⦋0⦌) (i j : Fin (m + 1)) (hij : i ≤ j) :
    simplexFibreMap X f x ≫ simplexFibreEdge X (x ∘ f.toOrderHom) i j hij =
      simplexFibreEdge X x (f.toOrderHom i) (f.toOrderHom j) (f.toOrderHom.monotone hij) := by
  have hf : SimplexCategory.mkOfLe i j hij ≫ f =
      SimplexCategory.mkOfLe (f.toOrderHom i) (f.toOrderHom j) (f.toOrderHom.monotone hij) := by
    ext k
    fin_cases k <;> rfl
  refine pullback.hom_ext ((Category.assoc _ _ _).trans
    (((congrArg _ (simplexFibreEdge_fst X _ i j hij)).trans ?_).trans
      (simplexFibreEdge_fst X x _ _ _).symm)) (stdSimplex.isTerminalObj₀.hom_ext _ _)
  rw [simplexFibreMap_ι_assoc, ← NatTrans.comp_app, ← pre_map,
    ← CategoryTheory.Functor.map_comp stdSimplex, hf]

end SimplexFibre

section SpineFibre

variable (X : SSet.{u})

noncomputable abbrev spineFibre {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) : SSet.{u} :=
  ihomFibre (spineSubcomplex.spineId n).vertex X x

noncomputable def simplexFibreSegalMap {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) :
    simplexFibre X x ⟶ spineFibre X x :=
  ihomFibre.map (spineSubcomplex n).ι id (fun _ ↦ rfl) X x

@[reassoc (attr := simp)]
lemma simplexFibreSegalMap_ι {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) :
    simplexFibreSegalMap X x ≫ ihomFibre.ι _ X x =
      ihomFibre.ι _ X x ≫ (pre (spineSubcomplex n).ι).app X :=
  ihomFibre.map_ι _ _ _ _ _

theorem rlp_I_simplexFibreSegalMap [X.Quasicategory] {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) :
    modelCategoryQuillen.I.rlp (simplexFibreSegalMap X x) :=
  MorphismProperty.of_isPullback
    (ihomFibre.isPullback_map (spineSubcomplex n).ι (spineSubcomplex.spineId n).vertex
      stdSimplex.obj₀Equiv.symm (fun _ ↦ rfl) X x)
    (rlp_I_pre_app_of_innerAnodyneExtensions (innerAnodyneExtensions_spineSubcomplex_ι n) X)

private noncomputable def spineEdge {n : ℕ} (i : Fin (n + 1)) :
    Δ[1] ⟶ (spineSubcomplex.{u} (n + 1) : SSet) :=
  yonedaEquiv.symm ((spineSubcomplex.spineId (n + 1)).arrow i)

private lemma spineEdge_ι {n : ℕ} (i : Fin (n + 1)) :
    spineEdge.{u} i ≫ (spineSubcomplex (n + 1)).ι =
      stdSimplex.map (SimplexCategory.mkOfLe i.castSucc i.succ (Fin.castSucc_le_succ i)) := by
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp, spineEdge, Equiv.apply_symm_apply]
  ext k
  fin_cases k <;> rfl

private lemma spineEdge_app {n : ℕ} (i : Fin (n + 1)) (k : Fin 2) :
    (spineEdge.{u} i).app _ (stdSimplex.obj₀Equiv.symm k) = (spineSubcomplex.spineId (n + 1)).vertex
      ((SimplexCategory.mkOfLe i.castSucc i.succ (Fin.castSucc_le_succ i)).toOrderHom k) := by
  refine Subtype.ext ?_
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm k))
    (spineEdge_ι.{u} i)
  refine h.trans ?_
  ext j
  fin_cases j
  fin_cases k <;> rfl

private noncomputable def spineFibreEdge {n : ℕ} (x : Fin (n + 2) → X _⦋0⦌) (i : Fin (n + 1)) :
    spineFibre X x ⟶ mappingSpace X (x i.castSucc) (x i.succ) :=
  ihomFibre.map (spineEdge i) _ (spineEdge_app i) X x ≫ (simplexFibreOneIso X _).hom

private lemma spineFibreEdge_fst {n : ℕ} (x : Fin (n + 2) → X _⦋0⦌) (i : Fin (n + 1)) :
    spineFibreEdge X x i ≫ pullback.fst _ _ = ihomFibre.ι _ X x ≫ (pre (spineEdge i)).app X :=
  (Category.assoc _ _ _).trans ((congrArg _ (simplexFibreOneIso_hom_fst X _)).trans
    (ihomFibre.map_ι _ _ _ X x))

private lemma yonedaEquiv_symm_comp_ihomSwap {T K : SSet.{u}} (c : T ⟶ (ihom K).obj X)
    (v : K _⦋0⦌) :
    yonedaEquiv.symm v ≫ ihomSwap T K X c = (ihomPointEquiv T X).symm (c ≫ evalVertex v X) :=
  (ihomPointEquiv T X).eq_symm_apply.2 ((ihomSwap_comp_evalVertex _ v).symm.trans
    (congrArg (· ≫ evalVertex v X) ((ihomSwap T K X).symm_apply_apply c)))

private lemma spinePath_aux {T M : SSet.{u}} (b : T ⟶ M) {f : M ⟶ (ihom Δ[1]).obj X}
    {s : M ⟶ Δ[0]} (k : Fin 2) (z : X _⦋0⦌)
    (h : f ≫ evalVertex (stdSimplex.obj₀Equiv.symm k) X = s ≫ yonedaEquiv.symm z) :
    (b ≫ f) ≫ evalVertex (stdSimplex.obj₀Equiv.symm k) X = const z :=
  (Category.assoc _ _ _).trans ((congrArg _ (h.trans ((congrArg (_ ≫ ·)
    (yonedaEquiv_symm_zero _)).trans (comp_const _ _)))).trans (comp_const _ _))

private noncomputable def spinePath {n : ℕ} {x : Fin (n + 2) → X _⦋0⦌} {T : SSet.{u}}
    (b : ∀ i : Fin (n + 1), T ⟶ mappingSpace X (x i.castSucc) (x i.succ)) :
    ((ihom T).obj X).Path (n + 1) where
  vertex k := yonedaEquiv ((ihomPointEquiv T X).symm (const (x k)))
  arrow i := yonedaEquiv (ihomSwap T Δ[1] X (b i ≫ pullback.fst _ _))
  arrow_src _ := (yonedaEquiv_naturality (SimplexCategory.δ (1 : Fin 2)) _).trans
    (congrArg yonedaEquiv ((congrArg (· ≫ _) stdSimplex_δ_one_eq).trans
      ((yonedaEquiv_symm_comp_ihomSwap X _ _).trans (congrArg _ (spinePath_aux X _ _ _
        (mappingSpace_fst_evalVertex_zero X _ _))))))
  arrow_tgt _ := (yonedaEquiv_naturality (SimplexCategory.δ (0 : Fin 2)) _).trans
    (congrArg yonedaEquiv ((congrArg (· ≫ _) stdSimplex_δ_zero_eq).trans
      ((yonedaEquiv_symm_comp_ihomSwap X _ _).trans (congrArg _ (spinePath_aux X _ _ _
        (mappingSpace_fst_evalVertex_one X _ _))))))

private lemma map_spineSubcomplexHomEquiv_symm {n : ℕ} {Z : SSet.{u}} (p : Z.Path (n + 1)) :
    (spineSubcomplex.spineId (n + 1)).map ((spineSubcomplexHomEquiv (n + 1) Z).symm p) = p :=
  (spineSubcomplexHomEquiv_apply _ _).symm.trans (Equiv.apply_symm_apply _ _)

private noncomputable def spineFibreLift {n : ℕ} {x : Fin (n + 2) → X _⦋0⦌} {T : SSet.{u}}
    (b : ∀ i : Fin (n + 1), T ⟶ mappingSpace X (x i.castSucc) (x i.succ)) :
    T ⟶ spineFibre X x :=
  ihomFibre.lift (ihomSwap _ T X ((spineSubcomplexHomEquiv (n + 1) _).symm (spinePath X b)))
    fun k ↦ (ihomSwap_comp_evalVertex _ _).trans ((congrArg (ihomPointEquiv T X)
      ((yonedaEquiv_symm_comp _ _).trans (congrArg (fun p ↦ yonedaEquiv.symm (p.vertex k))
        (map_spineSubcomplexHomEquiv_symm _)))).trans
      ((congrArg _ (Equiv.symm_apply_apply _ _)).trans (Equiv.apply_symm_apply _ _)))

private lemma spineFibreLift_edge {n : ℕ} {x : Fin (n + 2) → X _⦋0⦌} {T : SSet.{u}}
    (b : ∀ i : Fin (n + 1), T ⟶ mappingSpace X (x i.castSucc) (x i.succ)) (i : Fin (n + 1)) :
    spineFibreLift X b ≫ spineFibreEdge X x i = b i := by
  refine pullback.hom_ext ?_ (stdSimplex.isTerminalObj₀.hom_ext _ _)
  refine (Category.assoc _ _ _).trans ((congrArg _ (spineFibreEdge_fst X x i)).trans ?_)
  refine (ihomFibre.lift_ι_assoc _ _ _).trans ((ihomSwap T Δ[1] X).injective ?_)
  refine (ihomSwap_comp_pre_app _ _).trans ((congrArg (spineEdge i ≫ ·)
    ((ihomSwap _ T X).symm_apply_apply _)).trans ((yonedaEquiv_symm_comp _ _).trans ?_))
  exact (congrArg (fun p ↦ yonedaEquiv.symm (p.arrow i))
    (map_spineSubcomplexHomEquiv_symm (spinePath X b))).trans (yonedaEquiv.symm_apply_apply _)

private lemma spineFibre_hom_ext {n : ℕ} {x : Fin (n + 2) → X _⦋0⦌} {T : SSet.{u}}
    {f g : T ⟶ spineFibre X x} (h : ∀ i, f ≫ spineFibreEdge X x i = g ≫ spineFibreEdge X x i) :
    f = g := by
  refine ihomFibre.hom_ext ((ihomSwap T _ X).injective
    ((spineSubcomplexHomEquiv (n + 1) _).injective ?_))
  rw [spineSubcomplexHomEquiv_apply, spineSubcomplexHomEquiv_apply]
  refine Path.ext' fun i ↦ yonedaEquiv.symm.injective ?_
  have he (F : T ⟶ spineFibre X x) : yonedaEquiv.symm (((spineSubcomplex.spineId (n + 1)).map
      (ihomSwap T _ X (F ≫ ihomFibre.ι _ X x))).arrow i) =
        ihomSwap T Δ[1] X ((F ≫ spineFibreEdge X x i) ≫ pullback.fst _ _) :=
    (yonedaEquiv_symm_comp _ _).symm.trans ((ihomSwap_comp_pre_app _ _).symm.trans
      (congrArg _ (((Category.assoc _ _ _).trans (congrArg _ (spineFibreEdge_fst X x i).symm)).trans
        (Category.assoc _ _ _).symm)))
  exact (he f).trans ((congrArg (fun F ↦ ihomSwap T Δ[1] X (F ≫ pullback.fst _ _)) (h i)).trans
    (he g).symm)

noncomputable def simplexFibreSpineIso {n : ℕ} (x : Fin (n + 2) → X _⦋0⦌) :
    spineFibre X x ≅ ∏ᶜ fun i : Fin (n + 1) ↦ mappingSpace X (x i.castSucc) (x i.succ) where
  hom := Pi.lift (spineFibreEdge X x)
  inv := spineFibreLift X (Pi.π _)
  hom_inv_id := spineFibre_hom_ext X fun i ↦ by
    rw [Category.assoc, spineFibreLift_edge, Pi.lift_π, Category.id_comp]
  inv_hom_id := Pi.hom_ext _ _ fun i ↦ by
    rw [Category.assoc, Pi.lift_π, spineFibreLift_edge, Category.id_comp]

private lemma simplexFibreSpineIso_hom_π {n : ℕ} (x : Fin (n + 2) → X _⦋0⦌) (i : Fin (n + 1)) :
    (simplexFibreSpineIso X x).hom ≫ Pi.π _ i = spineFibreEdge X x i :=
  Pi.lift_π _ _

theorem simplexFibreSegalMap_simplexFibreSpineIso_π {n : ℕ} (x : Fin (n + 2) → X _⦋0⦌)
    (i : Fin (n + 1)) :
    simplexFibreSegalMap X x ≫ (simplexFibreSpineIso X x).hom ≫ Pi.π _ i =
      simplexFibreEdge X x i.castSucc i.succ (Fin.castSucc_le_succ i) := by
  refine pullback.hom_ext ?_ (stdSimplex.isTerminalObj₀.hom_ext _ _)
  rw [simplexFibreSpineIso_hom_π]
  refine (Category.assoc _ _ _).trans ((congrArg _ (spineFibreEdge_fst X x i)).trans
    ((simplexFibreSegalMap_ι_assoc X x _).trans ((congrArg _ ?_).trans
      (simplexFibreEdge_fst X x _ _ _).symm)))
  exact (NatTrans.comp_app _ _ _).symm.trans (congrArg (fun f ↦ f.app X)
    ((pre_map _ _).symm.trans (congrArg pre (spineEdge_ι i))))

noncomputable def simplexFibreSpineTwoIso (x : Fin 3 → X _⦋0⦌) :
    spineFibre X x ≅ mappingSpace X (x 0) (x 1) ⨯ mappingSpace X (x 1) (x 2) :=
  simplexFibreSpineIso X x ≪≫
    { hom := prod.lift (Pi.π _ 0) (Pi.π _ 1)
      inv := Pi.lift (Fin.cases prod.fst (Fin.cases prod.snd finZeroElim))
      hom_inv_id := Pi.hom_ext _ _ fun i ↦ by
        fin_cases i
        · exact (Category.assoc _ _ _).trans ((congrArg _ (Pi.lift_π _ _)).trans
            ((prod.lift_fst _ _).trans (Category.id_comp _).symm))
        · exact (Category.assoc _ _ _).trans ((congrArg _ (Pi.lift_π _ _)).trans
            ((prod.lift_snd _ _).trans (Category.id_comp _).symm))
      inv_hom_id := prod.hom_ext
        ((Category.assoc _ _ _).trans ((congrArg _ (prod.lift_fst _ _)).trans
          ((Pi.lift_π _ _).trans (Category.id_comp _).symm)))
        ((Category.assoc _ _ _).trans ((congrArg _ (prod.lift_snd _ _)).trans
          ((Pi.lift_π _ _).trans (Category.id_comp _).symm))) }

lemma simplexFibreSpineTwoIso_hom (x : Fin 3 → X _⦋0⦌) :
    (simplexFibreSpineTwoIso X x).hom =
      (simplexFibreSpineIso X x).hom ≫ prod.lift (Pi.π _ 0) (Pi.π _ 1) :=
  rfl

@[reassoc (attr := simp)]
lemma simplexFibreSegalMap_simplexFibreSpineTwoIso_fst (x : Fin 3 → X _⦋0⦌) :
    simplexFibreSegalMap X x ≫ (simplexFibreSpineTwoIso X x).hom ≫ prod.fst =
      simplexFibreEdge X x 0 1 (by decide) :=
  (congrArg _ ((Category.assoc _ _ _).trans (congrArg _ (prod.lift_fst _ _)))).trans
    (simplexFibreSegalMap_simplexFibreSpineIso_π X x 0)

@[reassoc (attr := simp)]
lemma simplexFibreSegalMap_simplexFibreSpineTwoIso_snd (x : Fin 3 → X _⦋0⦌) :
    simplexFibreSegalMap X x ≫ (simplexFibreSpineTwoIso X x).hom ≫ prod.snd =
      simplexFibreEdge X x 1 2 (by decide) :=
  (congrArg _ ((Category.assoc _ _ _).trans (congrArg _ (prod.lift_snd _ _)))).trans
    (simplexFibreSegalMap_simplexFibreSpineIso_π X x 1)

open modelCategoryQuillen in
private lemma kanComplex_piObj {m : ℕ} (F : Fin m → SSet.{u}) [∀ i, (F i).KanComplex] :
    (∏ᶜ F).KanComplex := by
  refine (isFibrant_iff _).2 ⟨?_⟩
  rw [fibrations_eq]
  intro _ _ _ hf
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  refine ⟨fun {t _} _ ↦ ⟨⟨{
    l := Pi.lift fun j ↦ (KanComplex.hornFilling (t ≫ Pi.π F j)).choose
    fac_left := Pi.hom_ext _ _ fun j ↦ ?_
    fac_right := by subsingleton }⟩⟩⟩
  rw [Category.assoc, Pi.lift_π]
  exact (KanComplex.hornFilling (t ≫ Pi.π F j)).choose_spec.symm

theorem rlp_monomorphisms_simplexFibreSegalMap_comp [X.Quasicategory] {n : ℕ}
    (x : Fin (n + 1) → X _⦋0⦌) {Y : SSet.{u}} (e : spineFibre X x ≅ Y) :
    (monomorphisms SSet.{u}).rlp (simplexFibreSegalMap X x ≫ e.hom) :=
  (monomorphisms _).rlp.comp_mem _ _
    (by rw [rlp_monomorphisms]; exact rlp_I_simplexFibreSegalMap X x) fun _ _ _ _ ↦ inferInstance

open modelCategoryQuillen in
theorem kanComplex_spineFibre [X.Quasicategory] {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) :
    (spineFibre X x).KanComplex := by
  cases n with
  | zero =>
    have hK : IsTerminal (spineSubcomplex.{u} 0 : SSet.{u}) :=
      stdSimplex.isTerminalObj₀.ofIso (Subcomplex.topIso _).symm
    exact (isFibrant_iff _).1
      ((isFibrant_iff_of_isTerminal (𝟙 _)
        (isTerminalIhomFibreOfIsTerminal hK _ X x)).2 inferInstance)
  | succ n =>
    have (i : Fin (n + 1)) : (mappingSpace X (x i.castSucc) (x i.succ)).KanComplex :=
      kanComplex_mappingSpace X _ _
    have := kanComplex_piObj fun i : Fin (n + 1) ↦ mappingSpace X (x i.castSucc) (x i.succ)
    exact isFibrant_of_fibration (simplexFibreSpineIso X x).hom

open modelCategoryQuillen in
theorem kanComplex_simplexFibre [X.Quasicategory] {n : ℕ} (x : Fin (n + 1) → X _⦋0⦌) :
    (simplexFibre X x).KanComplex := by
  have := kanComplex_spineFibre X x
  have : Fibration (simplexFibreSegalMap X x) := by
    rw [fibration_iff]
    exact MorphismProperty.antitone_rlp J_le_monomorphisms _
      (by rw [rlp_monomorphisms]; exact rlp_I_simplexFibreSegalMap X x)
  exact isFibrant_of_fibration (simplexFibreSegalMap X x)

end SpineFibre

end SSet
