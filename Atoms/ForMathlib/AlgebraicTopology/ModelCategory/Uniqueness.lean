import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.ModelCategory

universe v u

variable {C : Type u} [Category.{v} C]

theorem trivialFibrations_eq_of_cofibrations_eq (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C)) :
    (letI := M₁; trivialFibrations C) = (letI := M₂; trivialFibrations C) := by
  rw [← (letI := M₁; cofibrations_rlp (C := C)), ← (letI := M₂; cofibrations_rlp (C := C)), hc]

private theorem leftHomotopyRel_of_trivialFibrations_eq (M₁ M₂ : ModelCategory C)
    (ht : (letI := M₁; trivialFibrations C) = (letI := M₂; trivialFibrations C))
    {X Y : C} (hY : letI := M₁; IsFibrant Y) {f g : X ⟶ Y}
    (h : letI := M₁; LeftHomotopyRel f g) : letI := M₂; LeftHomotopyRel f g := by
  obtain ⟨P, hP, ⟨k⟩⟩ := (letI := M₁; h.exists_very_good_cylinder)
  have hπ : (letI := M₂; trivialFibrations C) (letI := M₁; P.π) := by
    rw [← ht]
    let := M₁
    exact mem_trivialFibrations P.π
  let := M₂
  exact ⟨{ toPrecylinder := (letI := M₁; P.toPrecylinder), weakEquivalence_π := ⟨hπ.2⟩ }, ⟨k⟩⟩

private theorem isCofibrant_iff_of_cofibrations_eq (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C)) (X : C) :
    (letI := M₁; IsCofibrant X) ↔ (letI := M₂; IsCofibrant X) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · let := M₁
    have h' := h.mem
    let := M₂
    exact ⟨hc ▸ h'⟩
  · let := M₂
    have h' := h.mem
    let := M₁
    exact ⟨hc ▸ h'⟩

theorem leftHomotopyRel_iff_of_cofibrations_eq_of_isFibrant_iff (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C))
    (hf : ∀ X : C, (letI := M₁; IsFibrant X) ↔ (letI := M₂; IsFibrant X))
    {X Y : C} (hY : letI := M₁; IsFibrant Y) (f g : X ⟶ Y) :
    (letI := M₁; LeftHomotopyRel f g) ↔ (letI := M₂; LeftHomotopyRel f g) := by
  have ht := trivialFibrations_eq_of_cofibrations_eq M₁ M₂ hc
  exact ⟨leftHomotopyRel_of_trivialFibrations_eq M₁ M₂ ht hY,
    leftHomotopyRel_of_trivialFibrations_eq M₂ M₁ ht.symm ((hf Y).1 hY)⟩

private theorem rightHomotopyRel_iff (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C))
    (hf : ∀ X : C, (letI := M₁; IsFibrant X) ↔ (letI := M₂; IsFibrant X))
    {X Y : C} (hX : letI := M₁; IsCofibrant X) (hY : letI := M₁; IsFibrant Y) (f g : X ⟶ Y) :
    (letI := M₁; RightHomotopyRel f g) ↔ (letI := M₂; RightHomotopyRel f g) := by
  have hX' := (isCofibrant_iff_of_cofibrations_eq M₁ M₂ hc X).1 hX
  have hY' := (hf Y).1 hY
  rw [← (letI := M₁; leftHomotopyRel_iff_rightHomotopyRel (f := f) (g := g)),
    ← (letI := M₂; leftHomotopyRel_iff_rightHomotopyRel (f := f) (g := g))]
  exact leftHomotopyRel_iff_of_cofibrations_eq_of_isFibrant_iff M₁ M₂ hc hf hY f g

private theorem weakEquivalences_of_bifibrant (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C))
    (hf : ∀ X : C, (letI := M₁; IsFibrant X) ↔ (letI := M₂; IsFibrant X))
    {X Y : C} (hXc : letI := M₁; IsCofibrant X) (hXf : letI := M₁; IsFibrant X)
    (hYc : letI := M₁; IsCofibrant Y) (hYf : letI := M₁; IsFibrant Y) (f : X ⟶ Y)
    (hw : (letI := M₁; weakEquivalences C) f) : (letI := M₂; weakEquivalences C) f := by
  obtain ⟨g, h₁, h₂⟩ :=
    (letI := M₁; haveI : WeakEquivalence f := ⟨hw⟩; RightHomotopyClass.whitehead f)
  have h₁' := (rightHomotopyRel_iff M₁ M₂ hc hf hXc hXf _ _).1 h₁
  have h₂' := (rightHomotopyRel_iff M₁ M₂ hc hf hYc hYf _ _).1 h₂
  have := (isCofibrant_iff_of_cofibrations_eq M₁ M₂ hc X).1 hXc
  have := (isCofibrant_iff_of_cofibrations_eq M₁ M₂ hc Y).1 hYc
  have := (hf X).1 hXf
  have := (hf Y).1 hYf
  let := M₂
  exact (weakEquivalence_of_rightHomotopyRel f g h₁' h₂').mem

private theorem weakEquivalences_of_fibrantReplacement (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C))
    (hf : ∀ X : C, (letI := M₁; IsFibrant X) ↔ (letI := M₂; IsFibrant X))
    {X R₁ : C} (hX : letI := M₁; IsCofibrant X) (hR₁ : letI := M₁; IsFibrant R₁) (j₁ : X ⟶ R₁)
    (hj₁ : (letI := M₁; trivialCofibrations C) j₁) : (letI := M₂; weakEquivalences C) j₁ := by
  let := M₂
  let φ := factorizationData (trivialCofibrations C) (fibrations C) (terminal.from X)
  have hR₂ : IsFibrant φ.Z := by
    rw [isFibrant_iff, Subsingleton.elim (terminal.from φ.Z) φ.p]
    exact ⟨φ.hp⟩
  have hX₂ : IsCofibrant X := (isCofibrant_iff_of_cofibrations_eq M₁ M₂ hc X).1 hX
  have : Cofibration φ.i := ⟨φ.hi.1⟩
  have : WeakEquivalence φ.i := ⟨φ.hi.2⟩
  have hR₂c : IsCofibrant φ.Z := isCofibrant_of_cofibration φ.i
  have hR₁f : IsFibrant R₁ := (hf R₁).1 hR₁
  have : Cofibration j₁ := ⟨hc ▸ hj₁.1⟩
  have hR₁c : IsCofibrant R₁ := isCofibrant_of_cofibration j₁
  let sq₂ : CommSq j₁ φ.i (terminal.from R₁) (terminal.from φ.Z) := ⟨terminal.hom_ext _ _⟩
  let s := sq₂.lift
  have hs : φ.i ≫ s = j₁ := sq₂.fac_left
  let := M₁
  have : Cofibration j₁ := ⟨hj₁.1⟩
  have : WeakEquivalence j₁ := ⟨hj₁.2⟩
  have hR₂₁ : IsFibrant φ.Z := (hf φ.Z).2 hR₂
  let sq₁ : CommSq φ.i j₁ (terminal.from φ.Z) (terminal.from R₁) := ⟨terminal.hom_ext _ _⟩
  let r := sq₁.lift
  have hr : j₁ ≫ r = φ.i := sq₁.fac_left
  have hrs : RightHomotopyRel (r ≫ s) (𝟙 R₁) := by
    rw [← RightHomotopyClass.mk_eq_mk_iff]
    apply (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence R₁ j₁).1
    simp only [RightHomotopyClass.precomp_mk, reassoc_of% hr, hs, Category.comp_id]
  have hrs₂ := (rightHomotopyRel_iff M₁ M₂ hc hf
    ((isCofibrant_iff_of_cofibrations_eq M₁ M₂ hc R₁).2 hR₁c) hR₁ _ _).1 hrs
  let := M₂
  have hsr : RightHomotopyRel (s ≫ r) (𝟙 φ.Z) := by
    rw [← RightHomotopyClass.mk_eq_mk_iff]
    apply (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence φ.Z φ.i).1
    simp only [RightHomotopyClass.precomp_mk, reassoc_of% hs, hr, Category.comp_id]
  have := weakEquivalence_of_rightHomotopyRel r s hrs₂ hsr
  have : WeakEquivalence (j₁ ≫ r) := by
    rw [hr]
    infer_instance
  exact (weakEquivalence_of_postcomp j₁ r).mem

private theorem mem_iff_of_comm (W : MorphismProperty C) [W.HasTwoOutOfThreeProperty]
    {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'} {a : X ⟶ X'} {b : Y ⟶ Y'}
    (sq : a ≫ f' = f ≫ b) (ha : W a) (hb : W b) : W f ↔ W f' := by
  constructor
  · intro hf
    exact W.of_precomp a f' ha (sq ▸ W.comp_mem f b hf hb)
  · intro hf
    exact W.of_postcomp f b hb (sq ▸ W.comp_mem a f' ha hf)

private theorem weakEquivalences_of_isCofibrant (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C))
    (hf : ∀ X : C, (letI := M₁; IsFibrant X) ↔ (letI := M₂; IsFibrant X))
    {X Y : C} (hX : letI := M₁; IsCofibrant X) (hY : letI := M₁; IsCofibrant Y) (f : X ⟶ Y)
    (hw : (letI := M₁; weakEquivalences C) f) : (letI := M₂; weakEquivalences C) f := by
  let := M₁
  let φ := factorizationData (trivialCofibrations C) (fibrations C) (terminal.from X)
  let ψ := factorizationData (trivialCofibrations C) (fibrations C) (terminal.from Y)
  have hφ : IsFibrant φ.Z := by
    rw [isFibrant_iff, Subsingleton.elim (terminal.from φ.Z) φ.p]
    exact ⟨φ.hp⟩
  have hψ : IsFibrant ψ.Z := by
    rw [isFibrant_iff, Subsingleton.elim (terminal.from ψ.Z) ψ.p]
    exact ⟨ψ.hp⟩
  have : Cofibration φ.i := ⟨φ.hi.1⟩
  have : WeakEquivalence φ.i := ⟨φ.hi.2⟩
  have : Cofibration ψ.i := ⟨ψ.hi.1⟩
  have hφc : IsCofibrant φ.Z := isCofibrant_of_cofibration φ.i
  have hψc : IsCofibrant ψ.Z := isCofibrant_of_cofibration ψ.i
  let sq : CommSq (f ≫ ψ.i) φ.i (terminal.from ψ.Z) (terminal.from φ.Z) :=
    ⟨terminal.hom_ext _ _⟩
  have hg : φ.i ≫ sq.lift = f ≫ ψ.i := sq.fac_left
  have hg₁ : weakEquivalences C sq.lift :=
    (mem_iff_of_comm _ hg φ.hi.2 ψ.hi.2).1 hw
  have hg₂ := weakEquivalences_of_bifibrant M₁ M₂ hc hf hφc hφ hψc hψ _ hg₁
  have hφ₂ := weakEquivalences_of_fibrantReplacement M₁ M₂ hc hf hX hφ φ.i φ.hi
  have hψ₂ := weakEquivalences_of_fibrantReplacement M₁ M₂ hc hf hY hψ ψ.i ψ.hi
  let := M₂
  exact (mem_iff_of_comm _ hg hφ₂ hψ₂).2 hg₂

private theorem weakEquivalences_le (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C))
    (hf : ∀ X : C, (letI := M₁; IsFibrant X) ↔ (letI := M₂; IsFibrant X)) :
    (letI := M₁; weakEquivalences C) ≤ (letI := M₂; weakEquivalences C) := by
  intro X Y f hw
  have ht := trivialFibrations_eq_of_cofibrations_eq M₁ M₂ hc
  let := M₁
  let φ := factorizationData (cofibrations C) (trivialFibrations C) (initial.to X)
  have hφc : IsCofibrant φ.Z := by
    rw [isCofibrant_iff, Subsingleton.elim (initial.to φ.Z) φ.i]
    exact ⟨φ.hi⟩
  let ψ := factorizationData (cofibrations C) (trivialFibrations C) (φ.p ≫ f)
  have : Cofibration ψ.i := ⟨ψ.hi⟩
  have hψc : IsCofibrant ψ.Z := isCofibrant_of_cofibration ψ.i
  have hφ₂ : (letI := M₂; trivialFibrations C) φ.p := ht ▸ φ.hp
  have hψ₂ : (letI := M₂; trivialFibrations C) ψ.p := ht ▸ ψ.hp
  have hg₁ : weakEquivalences C ψ.i :=
    (mem_iff_of_comm _ ψ.fac.symm φ.hp.2 ψ.hp.2).2 hw
  have hg₂ := weakEquivalences_of_isCofibrant M₁ M₂ hc hf hφc hψc _ hg₁
  let := M₂
  exact (mem_iff_of_comm _ ψ.fac.symm hφ₂.2 hψ₂.2).1 hg₂

theorem weakEquivalences_eq_of_cofibrations_eq_of_isFibrant_iff (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C))
    (hf : ∀ X : C, (letI := M₁; IsFibrant X) ↔ (letI := M₂; IsFibrant X)) :
    (letI := M₁; weakEquivalences C) = (letI := M₂; weakEquivalences C) :=
  le_antisymm (weakEquivalences_le M₁ M₂ hc hf)
    (weakEquivalences_le M₂ M₁ hc.symm fun X => (hf X).symm)

theorem fibrations_eq_of_cofibrations_eq_of_isFibrant_iff (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C))
    (hf : ∀ X : C, (letI := M₁; IsFibrant X) ↔ (letI := M₂; IsFibrant X)) :
    (letI := M₁; fibrations C) = (letI := M₂; fibrations C) := by
  have hw := weakEquivalences_eq_of_cofibrations_eq_of_isFibrant_iff M₁ M₂ hc hf
  have htc : (letI := M₁; trivialCofibrations C) = (letI := M₂; trivialCofibrations C) :=
    congrArg₂ (· ⊓ ·) hc hw
  rw [← (letI := M₁; trivialCofibrations_rlp (C := C)),
    ← (letI := M₂; trivialCofibrations_rlp (C := C)), htc]

theorem eq_of_cofibrations_eq_of_isFibrant_iff (M₁ M₂ : ModelCategory C)
    (hc : (letI := M₁; cofibrations C) = (letI := M₂; cofibrations C))
    (hf : ∀ X : C, (letI := M₁; IsFibrant X) ↔ (letI := M₂; IsFibrant X)) : M₁ = M₂ := by
  have hw := weakEquivalences_eq_of_cofibrations_eq_of_isFibrant_iff M₁ M₂ hc hf
  have hp := fibrations_eq_of_cofibrations_eq_of_isFibrant_iff M₁ M₂ hc hf
  obtain ⟨⟨F₁⟩, ⟨C₁⟩, ⟨W₁⟩⟩ := M₁
  obtain ⟨⟨F₂⟩, ⟨C₂⟩, ⟨W₂⟩⟩ := M₂
  obtain rfl : F₁ = F₂ := hp
  obtain rfl : C₁ = C₂ := hc
  obtain rfl : W₁ = W₂ := hw
  rfl

end HomotopicalAlgebra.ModelCategory
