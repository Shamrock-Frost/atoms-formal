import Atoms.ForMathlib.CategoryTheory.Limits.FunctorCategory.Filtered
import Atoms.Homotopical.Simplicial.Cells
import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace Atoms.Homotopical

open PartialOrder

def chainMax (n : SimplexCategory) :
    NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) →o ULift.{u} (Fin (n.len + 1)) where
  toFun S := S.finset.max' S.nonempty
  monotone' _ _ h := Finset.max'_subset _ h

theorem max'_map {X Y : Type*} [LinearOrder X] [LinearOrder Y] (S : NonemptyFiniteChains X)
    (f : X →o Y) : (S.map f).finset.max' (S.map f).nonempty = f (S.finset.max' S.nonempty) := by
  classical
  convert Finset.max'_image f.monotone S.finset (S.nonempty.image f) using 2
  ext y
  simp [PartialOrder.NonemptyFiniteChains.mem_map_iff]

theorem chainMax_map {n m : SimplexCategory} (θ : n ⟶ m)
    (S : NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1)))) :
    (chainMax m (NonemptyFiniteChains.map S (SimplexCategory.toPartOrd.map θ).hom)).down =
      θ.toOrderHom (chainMax n S).down :=
  congrArg ULift.down (max'_map (X := ULift.{u} (Fin (n.len + 1)))
    (Y := ULift.{u} (Fin (m.len + 1))) S (SimplexCategory.toPartOrd.map θ).hom)

noncomputable def simplexLastVertex : SimplexCategory.sd.{u} ⟶ SSet.stdSimplex.{u} where
  app n := nerveMap (chainMax n).monotone.functor ≫ (SSet.stdSimplex.isoNerve n.len).inv
  naturality n m θ := by
    induction n using SimplexCategory.rec with | _ n
    induction m using SimplexCategory.rec with | _ m
    ext d x
    induction d using Opposite.rec with | _ d
    induction d using SimplexCategory.rec with | _ d
    apply SSet.stdSimplex.ext
    intro i
    change ((nerveMap (chainMax ⦋m⦌).monotone.functor ≫ (SSet.stdSimplex.isoNerve m).inv).app _
      ((SimplexCategory.sd.map θ).app _ x)) i = (SSet.stdSimplex.map θ).app _
        ((nerveMap (chainMax ⦋n⦌).monotone.functor ≫ (SSet.stdSimplex.isoNerve n).inv).app _ x) i
    exact chainMax_map θ _

noncomputable def lastVertex : SSet.sd.{u} ⟶ 𝟭 SSet.{u} :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv (𝟭 SSet.{u}) simplexLastVertex

theorem sdIso_inv_app_lastVertex_app (n : SimplexCategory) :
    SSet.stdSimplex.sdIso.inv.app n ≫ lastVertex.{u}.app (SSet.stdSimplex.obj n) =
      simplexLastVertex.app n :=
  SSet.sd.descOfIsLeftKanExtension_fac_app SSet.stdSimplex.sdIso.inv (𝟭 SSet.{u})
    simplexLastVertex n

noncomputable def exUnit : 𝟭 SSet.{u} ⟶ SSet.ex.{u} :=
  SSet.sdExAdjunction.unit ≫ Functor.whiskerRight lastVertex SSet.ex ≫
    (Functor.leftUnitor SSet.ex).hom

theorem sdExAdjunction_homEquiv_lastVertex_app (X : SSet.{u}) :
    SSet.sdExAdjunction.homEquiv X X (lastVertex.app X) = exUnit.app X := by
  simp [Adjunction.homEquiv_unit, exUnit]

def chainIic (n : SimplexCategory) :
    ULift.{u} (Fin (n.len + 1)) →o NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) where
  toFun i :=
    { finset := Finset.univ.filter (· ≤ i)
      nonempty := ⟨i, by simp⟩
      comparable a b := le_total a.1 b.1 }
  monotone' _ _ h _ hx := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans h

@[simp]
theorem mem_chainIic {n : SimplexCategory} (i a : ULift.{u} (Fin (n.len + 1))) :
    a ∈ (chainIic n i).finset ↔ a ≤ i := by
  change a ∈ Finset.univ.filter (· ≤ i) ↔ _
  simp

theorem chainMax_chainIic (n : SimplexCategory) (i : ULift.{u} (Fin (n.len + 1))) :
    chainMax n (chainIic n i) = i :=
  le_antisymm (Finset.max'_le _ (chainIic n i).nonempty _ fun _ h ↦ (mem_chainIic _ _).1 h)
    (Finset.le_max' _ _ ((mem_chainIic _ _).2 le_rfl))

instance epi_simplexLastVertex_app (n : SimplexCategory) : Epi (simplexLastVertex.app n) := by
  induction n using SimplexCategory.rec with | _ n
  rw [NatTrans.epi_iff_epi_app]
  intro d
  induction d using Opposite.rec with | _ d
  induction d using SimplexCategory.rec with | _ d
  rw [epi_iff_surjective]
  intro y
  refine ⟨((SSet.stdSimplex.isoNerve n).hom.app _ y) ⋙ (chainIic ⦋n⦌).monotone.functor, ?_⟩
  apply SSet.stdSimplex.ext
  intro i
  exact congrArg ULift.down (chainMax_chainIic ⦋n⦌ (ULift.up (y i)))

instance epi_lastVertex_app_stdSimplex (n : SimplexCategory) :
    Epi (lastVertex.app (SSet.stdSimplex.obj n)) := by
  have : Epi (SSet.stdSimplex.sdIso.inv.app n ≫ lastVertex.app (SSet.stdSimplex.obj n)) := by
    rw [sdIso_inv_app_lastVertex_app]
    infer_instance
  exact epi_of_epi (SSet.stdSimplex.sdIso.inv.app n) _

theorem mono_of_cancel_stdSimplex {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : ∀ (m : ℕ) (g h : Δ[m] ⟶ X), g ≫ f = h ≫ f → g = h) : Mono f := by
  rw [NatTrans.mono_iff_mono_app]
  intro m
  induction m using Opposite.rec with | _ m
  induction m using SimplexCategory.rec with | _ m
  rw [mono_iff_injective]
  intro x y hxy
  apply SSet.yonedaEquiv.symm.injective
  apply hf
  rw [SSet.yonedaEquiv_symm_comp, SSet.yonedaEquiv_symm_comp, hxy]

instance mono_exUnit_app (X : SSet.{u}) : Mono (exUnit.app X) := by
  apply mono_of_cancel_stdSimplex
  intro m g h hgh
  have key (g : Δ[m] ⟶ X) : (SSet.sdExAdjunction.homEquiv _ X).symm (g ≫ exUnit.app X) =
      lastVertex.app (SSet.stdSimplex.obj ⦋m⦌) ≫ g := by
    rw [Adjunction.homEquiv_naturality_left_symm, ← sdExAdjunction_homEquiv_lastVertex_app,
      Equiv.symm_apply_apply]
    exact lastVertex.naturality g
  have := key g
  rw [hgh, key h] at this
  exact (cancel_epi _).1 this.symm

noncomputable def nMap {X Y : SSet.{u}} (f : X ⟶ Y) : X.N →o Y.N where
  toFun x := (x.toS.map f).toN
  monotone' x y h := by
    rw [SSet.N.le_iff, SSet.S.subcomplex_toN, SSet.S.subcomplex_toN]
    exact (SSet.Subcomplex.image_ofSimplex _ f).symm.trans_le
      ((SSet.Subcomplex.image_monotone f h).trans_eq (SSet.Subcomplex.image_ofSimplex _ f))

theorem subcomplex_nMap {X Y : SSet.{u}} (f : X ⟶ Y) (x : X.N) :
    (nMap f x).subcomplex = x.subcomplex.image f := by
  change (x.toS.map f).toN.subcomplex = _
  rw [SSet.S.subcomplex_toN]
  exact (SSet.Subcomplex.image_ofSimplex _ f).symm

theorem nMap_id (X : SSet.{u}) : nMap (𝟙 X) = OrderHom.id := by
  ext x
  apply SSet.N.subcomplex_injective
  rw [subcomplex_nMap, SSet.Subcomplex.image_id]
  rfl

theorem nMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    nMap (f ≫ g) = (nMap g).comp (nMap f) := by
  ext x
  apply SSet.N.subcomplex_injective
  change _ = (nMap g (nMap f x)).subcomplex
  rw [subcomplex_nMap, subcomplex_nMap, subcomplex_nMap, SSet.Subcomplex.image_comp]

noncomputable def nerveN : SSet.{u} ⥤ SSet.{u} where
  obj X := nerve X.N
  map f := nerveMap (nMap f).monotone.functor
  map_id X := by
    ext d x
    exact DFunLike.congr_fun (nMap_id X) _
  map_comp f g := by
    ext d x
    exact DFunLike.congr_fun (nMap_comp f g) _

def simplexVertices {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) : Finset (Fin (n + 1)) :=
  Finset.univ.image (fun i ↦ x i)

theorem mem_simplexVertices {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) (j : Fin (n + 1)) :
    j ∈ simplexVertices x ↔ ∃ i, x i = j := by
  simp [simplexVertices]

theorem simplexVertices_eq_nonDegenerateEquiv' {n d : ℕ}
    (x : (Δ[n] : SSet.{u}).nonDegenerate d) :
    simplexVertices x.1 = (SSet.stdSimplex.nonDegenerateEquiv' x).1 := by
  ext j
  rw [mem_simplexVertices, SSet.stdSimplex.nonDegenerateEquiv'_iff]

theorem simplexVertices_map_of_epi {n d e : ℕ} (g : ⦋e⦌ ⟶ ⦋d⦌) [Epi g]
    (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    simplexVertices ((Δ[n] : SSet.{u}).map g.op x) = simplexVertices x := by
  have hg := SimplexCategory.epi_iff_surjective.1 (inferInstance : Epi g)
  ext j
  rw [mem_simplexVertices, mem_simplexVertices]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨g.toOrderHom i, rfl⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨i', rfl⟩ := hg i
    exact ⟨i', rfl⟩

theorem ofSimplex_eq_face {n d : ℕ} (x : (Δ[n] : SSet.{u}) _⦋d⦌) :
    SSet.Subcomplex.ofSimplex x = SSet.stdSimplex.face (simplexVertices x) := by
  have h₁ := SSet.S.subcomplex_toN (SSet.S.mk x)
  have h₂ := SSet.S.map_toNπ_op_apply (SSet.S.mk x)
  set y := (SSet.S.mk x).toN
  calc SSet.Subcomplex.ofSimplex x = SSet.Subcomplex.ofSimplex y.simplex := h₁.symm
    _ = SSet.stdSimplex.face (SSet.stdSimplex.nonDegenerateEquiv' ⟨y.simplex, y.nonDegenerate⟩) :=
        (SSet.stdSimplex.face_nonDegenerateEquiv'.{u} ⟨y.simplex, y.nonDegenerate⟩).symm
    _ = SSet.stdSimplex.face (simplexVertices y.simplex) := by
        rw [simplexVertices_eq_nonDegenerateEquiv' ⟨y.simplex, y.nonDegenerate⟩]
    _ = SSet.stdSimplex.face (simplexVertices x) := by
        congr 1
        change _ = simplexVertices (SSet.S.mk x).simplex
        rw [← h₂, simplexVertices_map_of_epi]

theorem face_injective {n : ℕ} {S T : Finset (Fin (n + 1))}
    (h : SSet.stdSimplex.face.{u} S = SSet.stdSimplex.face T) : S = T :=
  le_antisymm ((SSet.stdSimplex.face_le_face_iff _ _).1 h.le)
    ((SSet.stdSimplex.face_le_face_iff _ _).1 h.ge)

def nVertices {n : ℕ} (x : (Δ[n] : SSet.{u}).N) : {S : Finset (Fin (n + 1)) // S.Nonempty} :=
  ⟨simplexVertices x.simplex, ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩⟩

theorem nVertices_le_iff {n : ℕ} (x y : (Δ[n] : SSet.{u}).N) :
    nVertices x ≤ nVertices y ↔ x ≤ y := by
  rw [SSet.N.le_iff]
  change _ ↔ SSet.Subcomplex.ofSimplex x.simplex ≤ SSet.Subcomplex.ofSimplex y.simplex
  rw [ofSimplex_eq_face, ofSimplex_eq_face, SSet.stdSimplex.face_le_face_iff]
  rfl

theorem nVertices_surjective (n : ℕ) : Function.Surjective (nVertices (n := n)) := by
  rintro ⟨S, hS⟩
  obtain ⟨d, hd⟩ : ∃ d, S.card = d + 1 :=
    ⟨S.card - 1, (Nat.succ_pred_eq_of_pos hS.card_pos).symm⟩
  let x := (SSet.stdSimplex.nonDegenerateEquiv' (n := n) (d := d)).symm ⟨S, hd⟩
  refine ⟨SSet.N.mk x.1 x.2, Subtype.ext ?_⟩
  change simplexVertices x.1 = S
  rw [simplexVertices_eq_nonDegenerateEquiv', Equiv.apply_symm_apply]

noncomputable def stdSimplexNOrderIso (n : ℕ) :
    (Δ[n] : SSet.{u}).N ≃o {S : Finset (Fin (n + 1)) // S.Nonempty} where
  toEquiv := Equiv.ofBijective nVertices
    ⟨fun x y h ↦ le_antisymm ((nVertices_le_iff x y).1 h.le) ((nVertices_le_iff y x).1 h.ge),
      nVertices_surjective n⟩
  map_rel_iff' := nVertices_le_iff _ _

def chainOrderIso (n : ℕ) :
    NonemptyFiniteChains (ULift.{u} (Fin (n + 1))) ≃o {S : Finset (Fin (n + 1)) // S.Nonempty} where
  toFun S := ⟨S.finset.map Equiv.ulift.toEmbedding, S.nonempty.map⟩
  invFun T :=
    { finset := T.1.map Equiv.ulift.symm.toEmbedding
      nonempty := T.2.map
      comparable a b := le_total a.1 b.1 }
  left_inv S := by
    ext a
    simp
  right_inv T := by
    ext a
    simp
  map_rel_iff' := Finset.map_subset_map

theorem nVertices_nMap {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌) (x : (Δ[n] : SSet.{u}).N) :
    (nVertices (nMap (SSet.stdSimplex.map θ) x)).1 = (nVertices x).1.image θ.toOrderHom := by
  apply face_injective
  change SSet.stdSimplex.face (simplexVertices (nMap (SSet.stdSimplex.map θ) x).simplex) = _
  rw [← ofSimplex_eq_face]
  change (nMap (SSet.stdSimplex.map θ) x).subcomplex = _
  rw [subcomplex_nMap]
  change (SSet.Subcomplex.ofSimplex x.simplex).image _ = _
  rw [SSet.Subcomplex.image_ofSimplex, ofSimplex_eq_face]
  congr 1
  ext j
  simp only [mem_simplexVertices, nVertices, Finset.mem_image]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨x.simplex i, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

noncomputable def chainNOrderIso (n : SimplexCategory) :
    NonemptyFiniteChains (ULift.{u} (Fin (n.len + 1))) ≃o (SSet.stdSimplex.{u}.obj n).N :=
  (chainOrderIso n.len).trans (stdSimplexNOrderIso n.len).symm

theorem nVertices_chainNOrderIso (n : ℕ) (S : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    nVertices (chainNOrderIso ⦋n⦌ S) = chainOrderIso n S :=
  (stdSimplexNOrderIso n).apply_symm_apply _

theorem chainNOrderIso_map {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (S : NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) :
    chainNOrderIso ⦋m⦌ (NonemptyFiniteChains.map S (SimplexCategory.toPartOrd.map θ).hom) =
      nMap (SSet.stdSimplex.map θ) (chainNOrderIso ⦋n⦌ S) := by
  apply (stdSimplexNOrderIso m).injective
  apply Subtype.ext
  change (nVertices (chainNOrderIso ⦋m⦌ _)).1 = (nVertices (nMap _ _)).1
  rw [nVertices_nMap, nVertices_chainNOrderIso, nVertices_chainNOrderIso]
  ext v
  simp only [chainOrderIso, RelIso.coe_fn_mk, Equiv.coe_fn_mk, Finset.mem_map,
    Finset.mem_image, Equiv.toEmbedding_apply, Equiv.ulift_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := (S.mem_map_iff _ a).1 ha
    exact ⟨b.down, ⟨b, hb, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨_, (S.mem_map_iff _ _).2 ⟨b, hb, rfl⟩, rfl⟩

noncomputable def simplexSdToNerveN :
    SimplexCategory.sd.{u} ⟶ SSet.stdSimplex.{u} ⋙ nerveN where
  app n := nerveMap (chainNOrderIso n).monotone.functor
  naturality n m θ := by
    induction n using SimplexCategory.rec with | _ n
    induction m using SimplexCategory.rec with | _ m
    ext d x
    refine nerve.ext_of_isThin (funext fun i ↦ ?_)
    exact chainNOrderIso_map θ (x.obj i)

instance isIso_nerveMap_orderIso {P Q : Type u} [PartialOrder P] [PartialOrder Q] (e : P ≃o Q) :
    IsIso (nerveMap e.monotone.functor) :=
  ⟨nerveMap e.symm.monotone.functor,
    by ext d x; exact e.symm_apply_apply _,
    by ext d x; exact e.apply_symm_apply _⟩

theorem mono_nerveMap_of_injective {P Q : Type u} [PartialOrder P] [PartialOrder Q] (f : P →o Q)
    (hf : Function.Injective f) : Mono (nerveMap f.monotone.functor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro a b h
  exact nerve.ext_of_isThin (funext fun i ↦ hf (congrArg (fun c : (nerve Q).obj d ↦ c.obj i) h))

noncomputable def sdToNerveN : SSet.sd.{u} ⟶ nerveN :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv nerveN simplexSdToNerveN

theorem sdIso_inv_app_sdToNerveN_app (n : SimplexCategory) :
    SSet.stdSimplex.sdIso.inv.app n ≫ sdToNerveN.app (SSet.stdSimplex.obj n) =
      simplexSdToNerveN.app n :=
  SSet.sd.descOfIsLeftKanExtension_fac_app SSet.stdSimplex.sdIso.inv nerveN simplexSdToNerveN n

instance isIso_simplexSdToNerveN_app (n : SimplexCategory) :
    IsIso (simplexSdToNerveN.app n) :=
  isIso_nerveMap_orderIso (chainNOrderIso n)

instance isIso_sdToNerveN_app_stdSimplex (n : SimplexCategory) :
    IsIso (sdToNerveN.app (SSet.stdSimplex.obj n)) := by
  have : IsIso (SSet.stdSimplex.sdIso.inv.app n ≫ sdToNerveN.app (SSet.stdSimplex.obj n)) := by
    rw [sdIso_inv_app_sdToNerveN_app]
    infer_instance
  exact IsIso.of_isIso_comp_left (SSet.stdSimplex.sdIso.inv.app n) _

theorem nMap_of_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x : X.N) :
    nMap f x = SSet.N.mk' (x.toS.map f)
      ((SSet.nonDegenerate_iff_of_mono f x.simplex).2 x.nonDegenerate) :=
  SSet.S.toN_eq_iff.2 rfl

theorem nMap_le_nMap_iff {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (x y : X.N) :
    nMap f x ≤ nMap f y ↔ x ≤ y := by
  refine ⟨fun h ↦ ?_, fun h ↦ (nMap f).monotone h⟩
  rw [nMap_of_mono, nMap_of_mono] at h
  change x.toS.map f ≤ y.toS.map f at h
  change x.toS ≤ y.toS
  rw [SSet.S.le_iff] at h ⊢
  obtain ⟨g, hg⟩ := h
  change ⦋x.dim⦌ ⟶ ⦋y.dim⦌ at g
  change Y.map g.op (f.app _ y.simplex) = f.app _ x.simplex at hg
  refine ⟨g, (mono_iff_injective (f.app _)).1 inferInstance ?_⟩
  rw [← hg]
  exact (NatTrans.naturality_apply f g.op y.simplex)

noncomputable def nMapEmbedding {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] : X.N ↪o Y.N :=
  OrderEmbedding.ofMapLEIff (nMap f) (nMap_le_nMap_iff f)

instance mono_nerveN_map {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] : Mono (nerveN.map f) :=
  mono_nerveMap_of_injective (nMap f) (nMapEmbedding f).injective

theorem nMap_yonedaEquiv_symm_le {X : SSet.{u}} (x : X.N) (t : (Δ[x.dim] : SSet.{u}).N) :
    nMap (SSet.yonedaEquiv.symm x.simplex) t ≤ x := by
  rw [SSet.N.le_iff, subcomplex_nMap]
  refine (SSet.Subcomplex.image_le_range _ _).trans ?_
  rw [SSet.Subcomplex.range_eq_ofSimplex, Equiv.apply_symm_apply]

theorem exists_nerveMap_app_eq {P Q : Type u} [PartialOrder P] [PartialOrder Q] (φ : P ↪o Q)
    {d : SimplexCategoryᵒᵖ} (c : (nerve Q).obj d) (hc : ∀ i, c.obj i ∈ Set.range φ) :
    ∃ c' : (nerve P).obj d, (nerveMap φ.toOrderHom.monotone.functor).app d c' = c := by
  choose t ht using hc
  have hmono : Monotone t := fun i j hij ↦ by
    rw [← φ.le_iff_le, ht, ht]
    exact (c.map (homOfLE hij)).le
  exact ⟨hmono.functor, nerve.ext_of_isThin (funext ht)⟩

section Nonsingular

variable {X : SSet.{u}} [X.Nonsingular]

theorem exists_nMap_yonedaEquiv_symm_eq {x w : X.N} (h : w ≤ x) :
    ∃ t : (Δ[x.dim] : SSet.{u}).N, nMap (SSet.yonedaEquiv.symm x.simplex) t = w := by
  have := SSet.Nonsingular.mono' x.simplex x.nonDegenerate
  refine ⟨SSet.N.mk (SSet.stdSimplex.objEquiv.symm (SSet.N.monoOfLE h))
    ((SSet.stdSimplex.objEquiv_symm_mem_nonDegenerate_iff_mono _).2 inferInstance), ?_⟩
  rw [nMap_of_mono, SSet.N.ext_iff]
  change SSet.S.mk (X.map (SSet.N.monoOfLE h).op x.simplex) = w.toS
  rw [SSet.N.map_monoOfLE]

theorem exists_nerveN_map_app_eq {x : X.N} {d : SimplexCategoryᵒᵖ} (c : (nerve X.N).obj d)
    (hc : ∀ i, c.obj i ≤ x) :
    ∃ c' : (nerve (Δ[x.dim] : SSet.{u}).N).obj d,
      (nerveN.map (SSet.yonedaEquiv.symm x.simplex)).app d c' = c := by
  have := SSet.Nonsingular.mono' x.simplex x.nonDegenerate
  exact exists_nerveMap_app_eq (nMapEmbedding (SSet.yonedaEquiv.symm x.simplex)) c
    fun i ↦ exists_nMap_yonedaEquiv_symm_eq (hc i)

theorem exists_sd_map_app_eq (X : SSet.{u}) [X.Nonsingular] (d : SimplexCategoryᵒᵖ)
    (u : (SSet.sd.obj X).obj d) :
    ∃ (x : X.N) (a : (SSet.sd.obj Δ[x.dim]).obj d),
      (SSet.sd.map (SSet.yonedaEquiv.symm x.simplex)).app d a = u := by
  have h := isColimitOfPreserves ((evaluation _ _).obj d)
    (isColimitOfPreserves SSet.sd X.isColimitCoconeN')
  obtain ⟨x, a, ha⟩ := Types.jointly_surjective_of_isColimit h u
  exact ⟨x, a, ha⟩

theorem sd_map_app_eq_of_sdToNerveN (d : SimplexCategoryᵒᵖ) (u : (SSet.sd.obj X).obj d)
    (z : X.N) (hz : z = ((sdToNerveN.app X).app d u).obj (Fin.last _))
    (b : (SSet.sd.obj Δ[z.dim]).obj d)
    (hb : (nerveN.map (SSet.yonedaEquiv.symm z.simplex)).app d
      ((sdToNerveN.app Δ[z.dim]).app d b) = (sdToNerveN.app X).app d u) :
    (SSet.sd.map (SSet.yonedaEquiv.symm z.simplex)).app d b = u := by
  obtain ⟨x, a, rfl⟩ := exists_sd_map_app_eq X d u
  have := SSet.Nonsingular.mono' x.simplex x.nonDegenerate
  rw [natTrans_app_app_map_app sdToNerveN] at hz hb
  have hzx : z ≤ x := by
    rw [hz]
    exact nMap_yonedaEquiv_symm_le x _
  rw [← SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex hzx, Functor.map_comp]
  change (SSet.sd.map _).app d ((SSet.sd.map (SSet.stdSimplex.map (SSet.N.monoOfLE hzx))).app d b)
    = _
  congr 1
  apply (mono_iff_injective ((sdToNerveN.{u}.app Δ[x.dim]).app d)).1 inferInstance
  apply (mono_iff_injective ((nerveN.map (SSet.yonedaEquiv.symm x.simplex)).app d)).1
    inferInstance
  rw [← hb, natTrans_app_app_map_app sdToNerveN,
    ← SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex hzx, Functor.map_comp]
  rfl

theorem sdToNerveN_app_app_bijective (X : SSet.{u}) [X.Nonsingular] (d : SimplexCategoryᵒᵖ) :
    Function.Bijective ((sdToNerveN.app X).app d) := by
  have lift (c : (nerve X.N).obj d) : ∃ b : (SSet.sd.obj Δ[(c.obj (Fin.last _)).dim]).obj d,
      (nerveN.map (SSet.yonedaEquiv.symm (c.obj (Fin.last _)).simplex)).app d
        ((sdToNerveN.app _).app d b) = c := by
    obtain ⟨c', hc'⟩ := exists_nerveN_map_app_eq c
      (fun i ↦ (c.map (homOfLE (Fin.le_last i))).le)
    obtain ⟨b, rfl⟩ := ((isIso_iff_bijective ((sdToNerveN.app Δ[_]).app d)).1
      inferInstance).2 c'
    exact ⟨b, hc'⟩
  refine ⟨fun u v h ↦ ?_, fun c ↦ ?_⟩
  · obtain ⟨b, hb⟩ := lift ((sdToNerveN.app X).app d u)
    rw [← sd_map_app_eq_of_sdToNerveN d u _ rfl b hb,
      sd_map_app_eq_of_sdToNerveN d v _ (by rw [h]) b (by rw [hb, h])]
  · obtain ⟨b, hb⟩ := lift c
    exact ⟨_, by rw [natTrans_app_app_map_app sdToNerveN, hb]⟩

end Nonsingular

instance isIso_sdToNerveN_app (X : SSet.{u}) [X.Nonsingular] : IsIso (sdToNerveN.app X) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro d
  exact (isIso_iff_bijective _).2 (sdToNerveN_app_app_bijective X d)

noncomputable def sdIsoNerveN (X : SSet.{u}) [X.Nonsingular] :
    SSet.sd.obj X ≅ nerve X.N :=
  @asIso _ _ (SSet.sd.obj X) (nerveN.obj X) (sdToNerveN.app X) (isIso_sdToNerveN_app X)

theorem sd_map_sdIsoNerveN_hom {X Y : SSet.{u}} [X.Nonsingular] [Y.Nonsingular]
    (f : X ⟶ Y) :
    SSet.sd.map f ≫ (sdIsoNerveN Y).hom =
      (sdIsoNerveN X).hom ≫ nerveMap (nMap f).monotone.functor :=
  sdToNerveN.naturality f

instance mono_sd_map {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] : Mono (SSet.sd.map f) := by
  have hI : SSet.modelCategoryQuillen.I.{u} ≤
      (MorphismProperty.monomorphisms SSet.{u}).inverseImage SSet.sd := by
    rintro _ _ _ ⟨n⟩
    have : Mono (SSet.sd.map ∂Δ[n].ι ≫ (sdIsoNerveN Δ[n]).hom) := by
      rw [sd_map_sdIsoNerveN_hom]
      exact @mono_comp _ _ _ _ _ (sdIsoNerveN _).hom inferInstance
        (nerveMap (nMap _).monotone.functor) (mono_nerveN_map _)
    exact mono_of_mono _ (sdIsoNerveN Δ[n]).hom
  exact saturation_le _ _ hI f
    (saturation_I_eq_monomorphisms.ge f (MorphismProperty.monomorphisms.infer_property f))

end Atoms.Homotopical
