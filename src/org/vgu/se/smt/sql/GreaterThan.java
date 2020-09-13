/**************************************************************************
Copyright 2020 Vietnamese-German-University

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

@author: ngpbh
***************************************************************************/

package org.vgu.se.smt.sql;

public class GreaterThan implements Expression {
    private Expression left;
    private Expression right;
    final String TRUE = "(and (> %1$s %2$s) " + "    (not (or %3$s %4$s)))";
    final String FALSE = "(and (not (> %1$s %2$s)) "
        + "    (not (or %3$s %4$s)))";
    final String NULL = "(or %3$s %4$s)";

    public Expression getRight() {
        return right;
    }

    public void setRight(Expression right) {
        this.right = right;
    }

    public Expression getLeft() {
        return left;
    }

    public void setLeft(Expression left) {
        this.left = left;
    }

    @Override
    public String toTrue() {
        return String.format(TRUE, left.toExec(), right.toExec(), left.toNull(),
            right.toNull());
    }

    @Override
    public String toFalse() {
        return String.format(FALSE, left.toExec(), right.toExec(),
            left.toNull(), right.toNull());
    }

    @Override
    public String toNull() {
        return String.format(NULL, left.toNull(), right.toNull());
    }

    @Override
    public String toExec() {
        // TODO Auto-generated method stub
        return null;
    }
    

    @Override
    public String toString() {
        return String.format("%1$s > %2$s", left.toString(), right.toString());
    }
}
