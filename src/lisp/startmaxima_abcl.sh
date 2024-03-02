#!/bin/sh
export MAXIMA_IMAGESDIR_BIN=$MAXIMA_IMAGESDIR/binary-abcl
java -jar $MAXIMA_IMAGESDIR/binary-abcl/abcl.jar --noinform $MAXIMA_LISP_OPTIONS --eval '(load "'"$MAXIMA_IMAGESDIR/binary-abcl/defsystem.lisp"'")' --eval '(mk:add-registry-location "'"$MAXIMA_IMAGESDIR/binary-abcl"'")' --eval '(funcall (intern (symbol-name :operate-on-system) :mk) "maxima" :load :verbose nil)' --eval '(cl-user::run)' -- "$@"
