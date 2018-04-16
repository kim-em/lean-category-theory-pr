-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison

import tidy.applicable tidy.force tidy.at_least_one tidy.repeat_at_least_once tidy.tidy
import tidy.its
import tidy.auto_cast
import tidy.make_lemma

universes u v

open tactic

set_option formatter.hide_full_terms false

set_option pp.proofs false
