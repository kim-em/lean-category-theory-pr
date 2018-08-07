-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import tidy.at_least_one 
import tidy.applicable
import tidy.rewrite_all
import tidy.injections
import tidy.tidy
import tidy.transport

-- meta def obviously' := `[skip]

universes u v

open tactic

set_option formatter.hide_full_terms false

set_option pp.proofs false
