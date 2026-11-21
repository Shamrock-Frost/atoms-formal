import Atoms.Homotopical.Cellular.MonoSaturated
import Atoms.ForMathlib.CategoryTheory.SmallObject.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import Mathlib.Data.Fintype.Lattice

open CategoryTheory Limits MorphismProperty Simplicial MonoidalCategory

namespace Atoms.Homotopical

open SSet

universe u

theorem saturation_I_eq_monomorphisms :
    saturation.{u} SSet.modelCategoryQuillen.I.{u} = MorphismProperty.monomorphisms SSet.{u} := by
  refine le_antisymm (saturation_le _ _ SSet.modelCategoryQuillen.I_le_monomorphisms) ?_
  intro X Y i hi
  have : Mono i := hi
  have hmem := ((SSet.relativeCellComplexOfMono i).transfiniteCompositionOfShape'
    (I := SSet.modelCategoryQuillen.I.{u}) (fun _ ↦ ⟨_⟩)).mem
  have := IsCellularlyClosed.isStableUnderCoproducts.{u}
    (saturation.{u} SSet.modelCategoryQuillen.I.{u})
  have hle : (coproducts.{u} SSet.modelCategoryQuillen.I.{u}).pushouts ≤
      saturation.{u} SSet.modelCategoryQuillen.I.{u} := by
    rw [pushouts_le_iff, coproducts_le_iff]
    exact le_saturation _
  have :=
    IsStableUnderTransfiniteComposition.shrink₀ (saturation.{u} SSet.modelCategoryQuillen.I.{u})
  exact transfiniteCompositionsOfShape_le _ ℕ _
    (transfiniteCompositionsOfShape_monotone ℕ hle _ hmem)

section Faces

variable (P : SSet.{u} → Prop)
  (hiso : ∀ {X Y : SSet.{u}} (_ : X ≅ Y), P X → P Y)
  (hpush : ∀ {X₀ X₁ X₂ X : SSet.{u}} {f₁ : X₀ ⟶ X₁} {f₂ : X₀ ⟶ X₂} {g₁ : X₁ ⟶ X}
    {g₂ : X₂ ⟶ X}, IsPushout f₁ f₂ g₁ g₂ → Mono f₁ → P X₀ → P X₁ → P X₂ → P X)
  (h₀ : P (⊥_ SSet.{u})) (hΔ : ∀ m : ℕ, P Δ[m])

include hiso h₀ in
theorem prop_bot {X : SSet.{u}} : P (⊥ : X.Subcomplex).toSSet :=
  hiso (IsInitial.uniqueUpToIso initialIsInitial Subcomplex.isInitialBot) h₀

include hiso h₀ hΔ in
theorem prop_face {n : ℕ} (S : Finset (Fin (n + 1))) : P (stdSimplex.face S).toSSet := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · rw [stdSimplex.face_empty]
    exact prop_bot P hiso h₀
  · obtain ⟨d, hd⟩ : ∃ d, S.card = d + 1 := ⟨S.card - 1, by have := hS.card_pos; omega⟩
    exact hiso (stdSimplex.isoOfRepresentableBy
      (stdSimplex.faceRepresentableBy S d (S.orderIsoOfFin hd))) (hΔ d)

theorem face_inf_sup_face {n : ℕ} (S : Finset (Fin (n + 1)))
    (𝒮 : Finset (Finset (Fin (n + 1)))) :
    stdSimplex.face.{u} S ⊓ 𝒮.sup stdSimplex.face =
      (𝒮.image (S ⊓ ·)).sup stdSimplex.face := by
  induction 𝒮 using Finset.induction_on with
  | empty => simp
  | insert T 𝒮 _ ih =>
    rw [Finset.sup_insert, Finset.image_insert, Finset.sup_insert, ← ih,
      ← stdSimplex.face_inter_face]
    ext U x
    simp only [Subfunctor.min_obj, Subfunctor.max_obj, Set.mem_inter_iff, Set.mem_union]
    tauto

include hiso hpush h₀ hΔ in
theorem prop_sup_face {n : ℕ} (𝒮 : Finset (Finset (Fin (n + 1)))) :
    P (𝒮.sup stdSimplex.face).toSSet := by
  suffices ∀ (k : ℕ) (𝒮 : Finset (Finset (Fin (n + 1)))), 𝒮.card ≤ k →
      P (𝒮.sup stdSimplex.face).toSSet from this _ 𝒮 le_rfl
  intro k
  induction k with
  | zero =>
    intro 𝒮 h
    rw [Finset.card_eq_zero.1 (Nat.le_zero.1 h), Finset.sup_empty]
    exact prop_bot P hiso h₀
  | succ k ih =>
    intro 𝒮 h𝒮
    rcases 𝒮.eq_empty_or_nonempty with rfl | ⟨S, hS⟩
    · exact ih ∅ (by simp)
    · have hcard : (𝒮.erase S).card ≤ k := by
        rw [Finset.card_erase_of_mem hS]
        omega
      rw [← Finset.insert_erase hS, Finset.sup_insert]
      have sq : Subcomplex.BicartSq (stdSimplex.face S ⊓ (𝒮.erase S).sup stdSimplex.face)
          (stdSimplex.face S) ((𝒮.erase S).sup stdSimplex.face)
          (stdSimplex.face S ⊔ (𝒮.erase S).sup stdSimplex.face) := ⟨rfl, rfl⟩
      refine hpush sq.isPushout inferInstance ?_ (prop_face P hiso h₀ hΔ S) (ih _ hcard)
      rw [face_inf_sup_face]
      exact ih _ (Finset.card_image_le.trans hcard)

include hiso hpush h₀ hΔ in
theorem prop_boundary (n : ℕ) : P (∂Δ[n] : SSet.{u}) := by
  have h : ∂Δ[n] = (Finset.univ.image fun i : Fin (n + 1) ↦ ({i}ᶜ : Finset _)).sup
      stdSimplex.face.{u} := by
    rw [boundary_eq_iSup, Finset.sup_image, Finset.sup_univ_eq_iSup]
    rfl
  rw [h]
  exact prop_sup_face P hiso hpush h₀ hΔ _

end Faces

theorem forall_of_stdSimplex {P : SSet.{u} → Prop} (hP : IsMonoSaturatedClass P)
    (hretract : ∀ {X Y : SSet.{u}} (i : X ⟶ Y) (r : Y ⟶ X), i ≫ r = 𝟙 X → P Y → P X)
    (hΔ : ∀ m : ℕ, P Δ[m]) (X : SSet.{u}) : P X :=
  forall_of_saturation_eq hP hretract SSet.modelCategoryQuillen.I.{u}
    saturation_I_eq_monomorphisms
    (fun _ hf ↦ by
      obtain ⟨n⟩ := hf
      exact ⟨prop_boundary P (fun e ↦ hP.of_iso e) hP.of_isPushout hP.initial hΔ n, hΔ n⟩) X

section Prism

variable {p q : ℕ}

def chainFace (S : Set (Fin (p + 1) × Fin (q + 1))) : (Δ[p] ⊗ Δ[q] : SSet.{u}).Subcomplex where
  obj _ := {x | ∀ i, prodStdSimplex.objEquiv x i ∈ S}
  map _ _ hx _ := hx _

theorem mem_chainFace_iff (S : Set (Fin (p + 1) × Fin (q + 1))) {U : SimplexCategoryᵒᵖ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).obj U) :
    x ∈ (chainFace S).obj U ↔ ∀ i, prodStdSimplex.objEquiv x i ∈ S := Iff.rfl

noncomputable def chainFaceRepresentableBy {d : ℕ} (φ : Fin (d + 1) ↪o Fin (p + 1) × Fin (q + 1)) :
    (chainFace (Set.range φ)).toSSet.RepresentableBy ⦋d⦌ where
  homEquiv {j} :=
    { toFun f := ⟨prodStdSimplex.objEquiv.{u}.symm (φ.toOrderHom.comp f.toOrderHom),
        fun i ↦ ⟨f.toOrderHom i, (congr($(prodStdSimplex.objEquiv.{u}.apply_symm_apply
          (φ.toOrderHom.comp f.toOrderHom)) i)).symm⟩⟩
      invFun x := SimplexCategory.Hom.mk
        { toFun i := φ.orderIso.symm ⟨prodStdSimplex.objEquiv x.1 i, x.2 i⟩
          monotone' _ _ h := φ.orderIso.symm.monotone ((prodStdSimplex.objEquiv x.1).monotone h) }
      left_inv f := by
        ext i : 3
        exact φ.orderIso.symm_apply_eq.2 (Subtype.ext (congr($(
          prodStdSimplex.objEquiv.{u}.apply_symm_apply (φ.toOrderHom.comp f.toOrderHom)) i)))
      right_inv x := by
        refine Subtype.ext (prodStdSimplex.objEquiv.{u}.injective (OrderHom.ext _ _
          (funext fun i ↦ ?_)))
        exact (congr($(prodStdSimplex.objEquiv.{u}.apply_symm_apply _) i)).trans
          (congrArg Subtype.val (φ.orderIso.apply_symm_apply ⟨_, x.2 i⟩)) }
  homEquiv_comp _ _ := rfl

noncomputable def chainFaceIso {d : ℕ} (φ : Fin (d + 1) ↪o Fin (p + 1) × Fin (q + 1)) :
    Δ[d] ≅ (chainFace (Set.range φ)).toSSet :=
  stdSimplex.isoOfRepresentableBy (chainFaceRepresentableBy φ)

def prismLevel (k l : ℕ) : Fin (1 + 1) :=
  ⟨if l ≤ k then 0 else 1, by split_ifs <;> omega⟩

variable (m : ℕ)

def prismEmb (k : Fin (m + 1)) : Fin (m + 2) ↪o Fin (1 + 1) × Fin (m + 1) :=
  OrderEmbedding.ofMapLEIff
    (fun l ↦ (prismLevel k l,
      ⟨if (l : ℕ) ≤ k then l else l - 1, by have := l.isLt; have := k.isLt; split_ifs <;> omega⟩))
    (fun a b ↦ by
      simp only [Prod.mk_le_mk, Fin.le_def, prismLevel]
      split_ifs <;> omega)

def interEmb (k : ℕ) : Fin (m + 1) ↪o Fin (1 + 1) × Fin (m + 1) :=
  OrderEmbedding.ofMapLEIff
    (fun l ↦ (prismLevel k l, l))
    (fun a b ↦ by
      simp only [Prod.mk_le_mk, Fin.le_def, prismLevel]
      split_ifs <;> omega)

variable {m}

theorem prismEmb_apply (k : Fin (m + 1)) (l : Fin (m + 2)) :
    prismEmb m k l = (prismLevel k l,
      ⟨if (l : ℕ) ≤ k then l else l - 1, by have := l.isLt; have := k.isLt; split_ifs <;> omega⟩) :=
  rfl

theorem interEmb_apply (k : ℕ) (l : Fin (m + 1)) :
    interEmb m k l = (prismLevel k l, l) :=
  rfl

theorem mem_range_prismEmb (k : Fin (m + 1)) (v : Fin (1 + 1) × Fin (m + 1)) :
    v ∈ Set.range (prismEmb m k) ↔
      ((v.1 : ℕ) = 0 → (v.2 : ℕ) ≤ k) ∧ ((v.1 : ℕ) = 1 → (k : ℕ) ≤ v.2) := by
  have h₁ := v.1.isLt
  have h₂ := v.2.isLt
  constructor
  · rintro ⟨l, rfl⟩
    have := l.isLt
    rw [prismEmb_apply]
    by_cases hl : (l : ℕ) ≤ k
    · simp [hl, prismLevel]
    · simp only [prismLevel, hl, ↓reduceIte]
      omega
  · intro h
    refine ⟨⟨if (v.1 : ℕ) = 0 then v.2 else v.2 + 1, by split_ifs <;> omega⟩, ?_⟩
    rw [prismEmb_apply]
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> dsimp only [prismLevel] <;> split_ifs <;> omega

theorem mem_range_interEmb (k : ℕ) (v : Fin (1 + 1) × Fin (m + 1)) :
    v ∈ Set.range (interEmb m k) ↔
      ((v.1 : ℕ) = 0 → (v.2 : ℕ) ≤ k) ∧ ((v.1 : ℕ) = 1 → k + 1 ≤ (v.2 : ℕ)) := by
  have h₁ := v.1.isLt
  constructor
  · rintro ⟨l, rfl⟩
    rw [interEmb_apply]
    by_cases hl : (l : ℕ) ≤ k
    · simp [hl, prismLevel]
    · simp only [prismLevel, hl, ↓reduceIte]
      omega
  · intro h
    refine ⟨v.2, ?_⟩
    rw [interEmb_apply]
    refine Prod.ext (Fin.ext ?_) rfl
    dsimp only [prismLevel]
    split_ifs <;> omega

variable (m)

def prismUnion (k : ℕ) : (Δ[1] ⊗ Δ[m] : SSet.{u}).Subcomplex where
  obj _ := {x | ∀ i, ((prodStdSimplex.objEquiv x i).1 : ℕ) = 0 →
    ((prodStdSimplex.objEquiv x i).2 : ℕ) ≤ k}
  map _ _ hx _ := hx _

variable {m}

theorem mem_prismUnion_iff (k : ℕ) {U : SimplexCategoryᵒᵖ} (x : (Δ[1] ⊗ Δ[m] : SSet.{u}).obj U) :
    x ∈ (prismUnion m k).obj U ↔
      ∀ i, ((prodStdSimplex.objEquiv x i).1 : ℕ) = 0 →
        ((prodStdSimplex.objEquiv x i).2 : ℕ) ≤ k := Iff.rfl

theorem prismUnion_zero : prismUnion m 0 = chainFace (Set.range (prismEmb m 0)) := by
  ext U x
  rw [mem_prismUnion_iff, mem_chainFace_iff]
  simp only [mem_range_prismEmb, Fin.val_zero]
  exact forall_congr' fun i ↦ ⟨fun h ↦ ⟨h, fun _ ↦ Nat.zero_le _⟩, fun h ↦ h.1⟩

theorem prismUnion_self : prismUnion m m = ⊤ :=
  le_antisymm le_top fun _ x _ i _ ↦ Nat.le_of_lt_succ (prodStdSimplex.objEquiv x i).2.isLt

theorem prismUnion_inf (k : ℕ) (hk : k + 1 < m + 1) :
    prismUnion m k ⊓ chainFace (Set.range (prismEmb m ⟨k + 1, hk⟩)) =
      chainFace (Set.range (interEmb m k)) := by
  ext U x
  simp only [Subfunctor.min_obj, Set.mem_inter_iff, mem_prismUnion_iff, mem_chainFace_iff,
    mem_range_prismEmb, mem_range_interEmb]
  constructor
  · intro h i
    exact ⟨h.1 i, (h.2 i).2⟩
  · intro h
    exact ⟨fun i ↦ (h i).1, fun i ↦ ⟨fun hi ↦ ((h i).1 hi).trans (Nat.le_succ k), (h i).2⟩⟩

theorem prismUnion_sup (k : ℕ) (hk : k + 1 < m + 1) :
    prismUnion m k ⊔ chainFace (Set.range (prismEmb m ⟨k + 1, hk⟩)) = prismUnion m (k + 1) := by
  ext U x
  simp only [Subfunctor.max_obj, Set.mem_union, mem_prismUnion_iff, mem_chainFace_iff,
    mem_range_prismEmb]
  constructor
  · rintro (h | h) i hi
    · exact (h i hi).trans (Nat.le_succ k)
    · exact (h i).1 hi
  · intro h
    by_cases h' : ∀ i, ((prodStdSimplex.objEquiv x i).1 : ℕ) = 0 →
        ((prodStdSimplex.objEquiv x i).2 : ℕ) ≤ k
    · exact Or.inl h'
    · push Not at h'
      obtain ⟨i, hi₀, hik⟩ := h'
      refine Or.inr fun j ↦ ⟨h j, fun hj₁ ↦ ?_⟩
      have hij : i ≤ j := by
        by_contra hji
        have := ((prodStdSimplex.objEquiv x).monotone (le_of_lt (not_le.1 hji))).1
        rw [Fin.le_def] at this
        omega
      have := ((prodStdSimplex.objEquiv x).monotone hij).2
      rw [Fin.le_def] at this
      have := h i hi₀
      omega

theorem prismUnion_bicartSq (k : ℕ) (hk : k + 1 < m + 1) :
    Subcomplex.BicartSq (chainFace (Set.range (interEmb m k))) (prismUnion m k)
      (chainFace (Set.range (prismEmb m ⟨k + 1, hk⟩))) (prismUnion m (k + 1)) := by
  rw [← prismUnion_inf k hk]
  exact ⟨prismUnion_sup k hk, rfl⟩

theorem prismUnion_mono {k k' : ℕ} (h : k ≤ k') : prismUnion m k ≤ prismUnion m k' :=
  fun _ _ hx i hi ↦ (hx i hi).trans h

theorem prism_of_isPushout (P : SSet.{u} → Prop)
    (hiso : ∀ {X Y : SSet.{u}} (_ : X ≅ Y), P X → P Y)
    (hpush : ∀ {X₀ X₁ X₂ X : SSet.{u}} {f₁ : X₀ ⟶ X₁} {f₂ : X₀ ⟶ X₂} {g₁ : X₁ ⟶ X}
      {g₂ : X₂ ⟶ X}, IsPushout f₁ f₂ g₁ g₂ → Mono f₁ → P X₀ → P X₁ → P X₂ → P X)
    (hΔ : ∀ m : ℕ, P Δ[m]) (m : ℕ) : P (Δ[1] ⊗ Δ[m]) := by
  have hface : ∀ {d : ℕ} (φ : Fin (d + 1) ↪o Fin (1 + 1) × Fin (m + 1)),
      P (chainFace (Set.range φ)).toSSet := fun φ ↦ hiso (chainFaceIso φ) (hΔ _)
  have key : ∀ k ≤ m, P (prismUnion m k).toSSet := by
    intro k hk
    induction k with
    | zero =>
      rw [prismUnion_zero]
      exact hface _
    | succ k ih =>
      exact hpush (prismUnion_bicartSq k (by omega)).isPushout inferInstance (hface _)
        (ih (by omega)) (hface _)
  have := key m le_rfl
  rw [prismUnion_self] at this
  exact hiso (Subcomplex.topIso _) this

end Prism

end Atoms.Homotopical
