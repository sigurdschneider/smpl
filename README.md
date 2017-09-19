# Coq Plugin smpl

Smpl is useful for proof automation in Coq. Smpl provides named lists
of tactics to which tactics can be added with Coq commands. A special
tactic called 'smpl foo' executes the tactics in the lists named foo
in order, until one of them succeeds. Smpl works across modules by
merging tactics from all imports according to a priority number that
can be provided upon addition. Smpl thus allows to modify the behavior
of a tactic after it is defined in a convenient and modular way.

Put differently, the realizes a that behaves similarily to 

    first [ l_1 | ... | l_n]
    
    
with the twist that the list `l_1 | ... | l_n` can be extended
in a fashion akin to eauto database (i.e. adding tactics works
across modules by merging the lists).

The plugin is available for Coq 8.6.1 in branch v8.6 and for 8.7 in
branch master.

See [the included demo file](theories/Demo.v) for instructions how to
use the plugin.

## Installation

If you are familiar with Coq plugins, this plugin will be no surprise
to you.

If you want to use the plugin you can clone it to an appropriate
place in your project directory.
You then need to enter the directory and build it:

    git clone https://github.com/sigurdschneider/smpl.git
    cd smpl
    make

**Note** that if you are using **Coq 8.6.1**, then you need to instead
use the folloing clone command, which specifies the branch to clone from:

    git clone -b v8.6 https://github.com/sigurdschneider/smpl.git

To use the plugin, you must add the following to your _CoqProject file:

    -R smpl/theories smpl
    -I smpl/src

In any of your files, you can then simply import the plugin via

    Require Import smpl.Smpl.


### Optional: Using git submodules

If you are using git for source management, you can include smpl
as a submodule:

    git submodule add https://github.com/sigurdschneider/smpl smpl
    cd smpl
    make

This will create .gitmodules and inform git that the the directory smpl
belongs to a different git repository.
