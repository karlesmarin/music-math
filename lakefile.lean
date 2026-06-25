import Lake
open Lake DSL

package «music_math» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Pinned to the Mathlib revision the development was built against (see lean-toolchain).
-- Run `lake exe cache get` before `lake build`.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "701fb6e9c3b9285968b375d19886bfc5ca134840"

-- The note's Lean sources live in lean/. SixThirty imports NeoRiemannian.
@[default_target]
lean_lib «NeoRiemannian» where
  srcDir := "lean"

@[default_target]
lean_lib «SixThirty» where
  srcDir := "lean"
