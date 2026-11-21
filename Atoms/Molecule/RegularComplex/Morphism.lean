import Atoms.Molecule.RegularComplex.AtomMorphism

universe u v

open Order Set Topology

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}} {f : P → Q}

theorem IsLocalEmbedding.injOn (hf : IsLocalEmbedding f) {x y z : P} (hy : y ≤ x) (hz : z ≤ x)
    (h : f y = f z) : y = z := by
  have hy' : y ∈ closure ({x} : Set P) := (Set.ext_iff.1 IsUpperSet.closure_singleton _).2 hy
  have hz' : z ∈ closure ({x} : Set P) := (Set.ext_iff.1 IsUpperSet.closure_singleton _).2 hz
  exact congrArg Subtype.val ((hf x).injective (a₁ := ⟨y, hy'⟩) (a₂ := ⟨z, hz'⟩) h)

theorem IsLocalEmbedding.grade_eq (hf : IsLocalEmbedding f) (x : P) :
    grade ℕ (f x) = grade ℕ x := by
  refine le_antisymm ((IsUpperSet.isClosedMap_iff_fibration.1 hf.isClosedMap).grade_apply_le x) ?_
  induction x using WellFoundedLT.induction with
  | _ x ih =>
    by_cases hx : IsMin x
    · rw [grade_eq_zero_iff.2 hx]
      exact Nat.zero_le _
    · obtain ⟨z, hz⟩ := not_isMin_iff.1 hx
      obtain ⟨y, -, hy⟩ := exists_le_covBy_of_lt hz
      have hdy := Nat.covBy_iff_add_one_eq.1 (hy.grade ℕ)
      have hlt : f y < f x :=
        lt_of_le_of_ne (hf.monotone hy.lt.le) fun h => hy.lt.ne (hf.injOn hy.lt.le le_rfl h)
      have := ih y hy.lt
      have := grade_strictMono (𝕆 := ℕ) hlt
      omega

theorem IsMap.isMorphism_of_grade_eq (hf : IsMap f) (hd : ∀ x, grade ℕ (f x) = grade ℕ x) :
    IsMorphism f where
  bijOn_faces x α := by
    rcases Nat.eq_zero_or_pos (grade ℕ x) with h0 | hx
    · have he : P.faces α x = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
        have := Nat.covBy_iff_add_one_eq.1 (hy.1.grade ℕ); omega
      have he' : Q.faces α (f x) = ∅ := Set.eq_empty_of_forall_notMem fun y hy => by
        have := Nat.covBy_iff_add_one_eq.1 (hy.1.grade ℕ); rw [hd] at this; omega
      rw [he, he']
      exact Set.bijOn_empty f
    set n := grade ℕ x - 1 with hn
    have h1 : grade ℕ x = n + 1 := by omega
    have h2 : grade ℕ (f x) = n + 1 := by rw [hd]; omega
    have hb := hf.image_boundary x n α
    have hanti {A : Set Q} (hA : ∀ a ∈ A, grade ℕ a = n) : IsAntichain (· ≤ ·) A :=
      fun a ha b hb hne hab => hne (GradeOrder.eq_of_le_of_grade_le hab (by rw [hA a ha, hA b hb]))
    have hA : ∀ a ∈ f '' P.faces α x, grade ℕ a = n := by
      rintro _ ⟨y, hy, rfl⟩
      have := Nat.covBy_iff_add_one_eq.1 (hy.1.grade ℕ)
      rw [hd]; omega
    have hB : ∀ b ∈ Q.faces α (f x), grade ℕ b = n := by
      intro b hb
      have := Nat.covBy_iff_add_one_eq.1 (hb.1.grade ℕ)
      omega
    have himg : f '' P.faces α x = Q.faces α (f x) := by
      have h := hb
      rw [boundary_Iic h1, boundary_Iic h2, hf.fibration.image_lowerClosure hf.monotone] at h
      ext w
      rw [← (hanti hA).maximal_mem_lowerClosure_iff_mem, SetLike.coe_injective h,
        (hanti hB).maximal_mem_lowerClosure_iff_mem]
    refine himg ▸ InjOn.bijOn_image fun y hy y' hy' h => ?_
    have hyB : y ∈ P.boundary (.Iic x) n α := by
      rw [boundary_Iic h1]; exact subset_lowerClosure hy
    have hy'B : y' ∈ P.boundary (.Iic x) n α := by
      rw [boundary_Iic h1]; exact subset_lowerClosure hy'
    have hz : f y ∈ (Q.boundary (.Iic (f x)) n α : Set Q) := hb ▸ mem_image_of_mem f hyB
    have hmem {w : P} (hw : w ∈ P.boundary (.Iic x) n α) (hfw : f y ≤ f w) : grade ℕ w = n := by
      refine le_antisymm (grade_le_of_mem_boundary hw) ?_
      rw [← hd, ← hA (f y) (mem_image_of_mem f hy)]
      exact grade_mono hfw
    exact IsUpperSet.subsingleton_of_isPreconnected_of_grade_eq
      ((hf.finalOn x n α).2 (f y) hz).isPreconnected (fun w hw => hmem hw.1 hw.2)
      ⟨hyB, le_rfl⟩ ⟨hy'B, h.le⟩

theorem IsMap.isMorphism_of_isLocalEmbedding (hf : IsMap f) (hle : IsLocalEmbedding f) :
    IsMorphism f :=
  hf.isMorphism_of_grade_eq hle.grade_eq

theorem IsMap.isMorphism_of_injective (hf : IsMap f) (hi : Function.Injective f) :
    IsMorphism f :=
  hf.isMorphism_of_isLocalEmbedding fun _ =>
    (IsClosedEmbedding.of_continuous_injective_isClosedMap
      (IsUpperSet.monotone_iff_continuous.1 hf.monotone) hi hf.isClosedMap).comp
      isClosed_closure.isClosedEmbedding_subtypeVal

theorem IsMorphism.isMap_of_isRDC (hf : IsMorphism f) (hP : IsRDC P) (hQ : IsRDC Q) :
    IsMap f := by
  have himg (x : P) (n : ℕ) (α : Bool) :
      f '' P.boundary (.Iic x) n α = Q.boundary (.Iic (f x)) n α := by
    rcases lt_or_ge n (grade ℕ x) with hn | hn
    · exact hf.image_boundary_of_isAtomIn ⟨hP x, x, rfl⟩ ⟨hQ (f x), f x, rfl⟩
        (hf.image_Iic x).subset
        (by rw [LowerSet.krullDim_Iic, LowerSet.krullDim_Iic, hf.grade_eq])
        (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hn) α
    · rw [boundary_eq_self (by rw [LowerSet.krullDim_Iic]; exact_mod_cast hn),
        boundary_eq_self (by rw [LowerSet.krullDim_Iic, hf.grade_eq]; exact_mod_cast hn),
        hf.image_Iic]
  refine ⟨hf.isClosedMap, fun x n α =>
    ⟨fun y hy => himg x n α ▸ mem_image_of_mem f hy, fun y hy => ?_⟩⟩
  rw [← himg] at hy
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  refine ⟨⟨y₀, hy₀, le_rfl⟩, IsUpperSet.isPreconnected_of_isLeast ⟨⟨hy₀, le_rfl⟩, fun c hc => ?_⟩⟩
  obtain ⟨z, hzc, hzy⟩ := hf.fibration hc.2
  obtain rfl := hf.eq_of_apply_eq_of_isAtomIn_of_isRDC hQ ⟨hP x, x, rfl⟩
    (hzc.trans (boundary_le (.Iic x) n α hc.1)) (boundary_le (.Iic x) n α hy₀) hzy
  exact hzc

theorem isMap_and_isLocalEmbedding_iff_isMorphism (hP : IsRDC P) (hQ : IsRDC Q)
    (f : P → Q) : IsMap f ∧ IsLocalEmbedding f ↔ IsMorphism f :=
  ⟨fun h => h.1.isMorphism_of_isLocalEmbedding h.2,
    fun hf => ⟨hf.isMap_of_isRDC hP hQ, hf.isLocalEmbedding_of_isRDC hP hQ⟩⟩

end Atoms.Molecule.OGP
