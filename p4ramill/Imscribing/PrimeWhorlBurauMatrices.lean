import Mathlib
import Imscribing.PrimeWhorlBurau

/-!
# Explicit unreduced Burau matrices and matrix Artin identities

This module isolates the 4×4 matrix calculations from the more elementary
fully invertible `Strand4` proofs. It is a literal transcription of the
JS `generator()` blocks. Compile this separately to audit the matrix simp
tactics with the fork's Mathlib version.
-/

namespace Imscribing.PrimeWhorl
namespace Burau

variable {R : Type*} [CommRing R]

/-- Literal 4×4 unreduced Burau matrices, matching the JS generator convention. -/
def matrix1 (t : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1-t, t, 0, 0;
     1,   0, 0, 0;
     0,   0, 1, 0;
     0,   0, 0, 1]

def matrix2 (t : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0,   0, 0;
     0, 1-t, t, 0;
     0, 1,   0, 0;
     0, 0,   0, 1]

def matrix3 (t : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0,   0;
     0, 1, 0,   0;
     0, 0, 1-t, t;
     0, 0, 1,   0]

/-- Literal inverse matrices, where `tinv` is *certified* by `UnitPhase`. -/
def inverseMatrix1 (u : R) : Matrix (Fin 4) (Fin 4) R :=
  !![0, 1,   0, 0;
     u, 1-u, 0, 0;
     0, 0,   1, 0;
     0, 0,   0, 1]

def inverseMatrix2 (u : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0,   0;
     0, 0, 1,   0;
     0, u, 1-u, 0;
     0, 0, 0,   1]

def inverseMatrix3 (u : R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, u, 1-u]

/-- The braid relations for the actual 4×4 matrices. These are polynomial
    identities in the single common phase `t`. -/
theorem matrix_braid12 (t : R) :
    matrix1 t * matrix2 t * matrix1 t =
    matrix2 t * matrix1 t * matrix2 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix1, matrix2, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem matrix_braid23 (t : R) :
    matrix2 t * matrix3 t * matrix2 t =
    matrix3 t * matrix2 t * matrix3 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix2, matrix3, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem matrix_braid13 (t : R) :
    matrix1 t * matrix3 t = matrix3 t * matrix1 t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix1, matrix3, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end Burau
end Imscribing.PrimeWhorl
