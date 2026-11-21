import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

universe u

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory

namespace SSet

abbrev cube (k : ℕ) : SSet.{u} := nerve (ULift.{u} (Fin k → Fin 2))

namespace cube

def face (k : ℕ) (j : Fin k) (ε : Fin 2) : (cube.{u} k).Subcomplex where
  obj _ := {z | ∀ t, (z.obj t).down j = ε}
  map _ _ hz _ := hz _

lemma mem_face_iff {k : ℕ} (j : Fin k) (ε : Fin 2) {n : SimplexCategoryᵒᵖ}
    (z : (cube.{u} k).obj n) : z ∈ (face k j ε).obj n ↔ ∀ t, (z.obj t).down j = ε :=
  Iff.rfl

def boundary (k : ℕ) : (cube.{u} k).Subcomplex :=
  ⨆ p : Fin k × Fin 2, face k p.1 p.2

end cube

def openBox (k : ℕ) (j : Fin k) (ε : Fin 2) : (cube.{u} k).Subcomplex :=
  ⨆ p : {p : Fin k × Fin 2 // p ≠ (j, ε)}, cube.face k p.1.1 p.1.2

namespace cube

variable {k : ℕ} (j : Fin (k + 1))

private def toProd : cube.{u} (k + 1) ⟶ Δ[1] ⊗ cube.{u} k :=
  lift (nerveMap (Monotone.functor (f := fun p : ULift.{u} (Fin (k + 1) → Fin 2) ↦
      (⟨p.down j⟩ : ULift.{u} (Fin 2))) fun _ _ h ↦ h j) ≫ (stdSimplex.isoNerve 1).inv)
    (nerveMap (Monotone.functor (f := fun p : ULift.{u} (Fin (k + 1) → Fin 2) ↦
      (⟨fun m ↦ p.down (j.succAbove m)⟩ : ULift.{u} (Fin k → Fin 2))) fun _ _ h _ ↦ h _))

private lemma toProd_app_fst {d : ℕ} (z : cube.{u} (k + 1) _⦋d⦌) (t : Fin (d + 1)) :
    ((toProd j).app _ z).1 t = (z.obj t).down j := rfl

private lemma toProd_app_snd {d : ℕ} (z : cube.{u} (k + 1) _⦋d⦌) (t : Fin (d + 1)) (m : Fin k) :
    (((toProd j).app _ z).2.obj t).down m = (z.obj t).down (j.succAbove m) := rfl

private instance : IsIso (toProd.{u} j) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun ⟨⟨d⟩⟩ ↦ ?_
  rw [isIso_iff_bijective]
  constructor
  · intro z z' h
    refine nerve.ext_of_isThin (funext fun t ↦ ULift.ext _ _ (funext fun m ↦ ?_))
    obtain rfl | ⟨m, rfl⟩ := j.eq_self_or_eq_succAbove m
    · rw [← toProd_app_fst, ← toProd_app_fst]
      exact congrArg (fun w ↦ w.1 t) h
    · rw [← toProd_app_snd, ← toProd_app_snd]
      exact congrArg (fun w ↦ (w.2.obj t).down m) h
  · rintro ⟨s, w⟩
    refine ⟨Monotone.functor (f := fun t ↦ ⟨j.insertNth (s t) (w.obj t).down⟩)
      fun t t' htt' ↦ ULift.up_le.2 (Fin.insertNth_le_iff.2 ⟨?_, fun m ↦ ?_⟩), ?_⟩
    · simp only [Fin.insertNth_apply_same]
      exact (stdSimplex.asOrderHom s).monotone htt'
    · simpa using (w.map (homOfLE htt')).le m
    · refine Prod.ext (stdSimplex.ext _ _ fun t ↦ ?_)
        (nerve.ext_of_isThin (funext fun t ↦ ULift.ext _ _ (funext fun m ↦ ?_)))
      · exact (toProd_app_fst _ _ _).trans
          (Fin.insertNth_apply_same (α := fun _ ↦ Fin 2) j (s t) (w.obj t).down)
      · exact (toProd_app_snd _ _ _ _).trans
          (Fin.insertNth_apply_succAbove (α := fun _ ↦ Fin 2) j (s t) (w.obj t).down m)

private lemma fin2_ne_iff (δ ε : Fin 2) : δ ≠ ε ↔ δ = ε.rev := by
  revert δ ε
  decide

private lemma fin2_rev_ne (a : Fin 2) : a.rev ≠ a := by
  revert a
  decide

private lemma mem_horn_one_iff {d : ℕ} (s : Δ[1] _⦋d⦌) (a : Fin 2) :
    s ∈ (Λ[1, a] : (Δ[1] : SSet.{u}).Subcomplex).obj _ ↔ ∀ t, s t = a := by
  rw [mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨b, hb, hs⟩ t
    by_contra ht
    exact hs ⟨t, ((fin2_ne_iff _ _).1 ht).trans ((fin2_ne_iff _ _).1 hb).symm⟩
  · intro hs
    refine ⟨a.rev, fin2_rev_ne a, ?_⟩
    rintro ⟨t, ht⟩
    exact fin2_rev_ne a (ht.symm.trans (hs t))

end cube

open cube in
private lemma openBox_succ (k : ℕ) (j : Fin (k + 1)) (ε : Fin 2) :
    openBox.{u} (k + 1) j ε =
      ((Λ[1, ε.rev] : (Δ[1] : SSet.{u}).Subcomplex).unionProd (cube.boundary k)).preimage
        (toProd j) := by
  ext ⟨⟨d⟩⟩ z
  refine Iff.trans ?_ (Subcomplex.mem_unionProd_iff (S := Λ[1, ε.rev]) (T := cube.boundary k)
    ((toProd j).app _ z)).symm
  simp only [openBox, cube.boundary, Subfunctor.iSup_obj, Set.mem_iUnion, mem_horn_one_iff,
    mem_face_iff, Subtype.exists, Prod.exists, ne_eq, Prod.mk.injEq, toProd_app_fst,
    toProd_app_snd]
  constructor
  · rintro ⟨m, δ, h, hz⟩
    obtain rfl | ⟨m, rfl⟩ := j.eq_self_or_eq_succAbove m
    · exact Or.inr fun t ↦ (hz t).trans ((fin2_ne_iff δ ε).1 fun h' ↦ h ⟨rfl, h'⟩)
    · exact Or.inl ⟨m, δ, hz⟩
  · rintro (⟨m, δ, hz⟩ | hz)
    · exact ⟨_, δ, fun h ↦ Fin.succAbove_ne j m h.1, hz⟩
    · exact ⟨j, ε.rev, fun h ↦ fin2_rev_ne ε h.2, hz⟩

theorem anodyneExtensions_openBox_ι (k : ℕ) (j : Fin k) (ε : Fin 2) :
    anodyneExtensions (openBox.{u} k j ε).ι := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by have := j.pos; lia⟩
  rw [openBox_succ]
  exact anodyneExtensions_preimage_ι _
    (anodyneExtensions_unionProd_ι' _ _ (anodyneExtensions.horn_ι _))

end SSet
