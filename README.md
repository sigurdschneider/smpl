# Coq Plugin smpl

A plugin that realizes a tactic similar to `first [ l_1 | ... | l_n ]`,
with the twist that the list `l_1 | ... | l_n` can be extended like an
eauto database.

See [the included demo file](theories/Demo.v).

The code is written for Coq 8.6. To make it work with 8.5, some modules
have to be changed. For example, CError.errorlabstrm was in a different
module in 8.5.