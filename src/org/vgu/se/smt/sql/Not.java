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

public class Not implements Expression {
    private Expression exp;

    public Expression getExp() {
        return exp;
    }

    public void setExp(Expression exp) {
        this.exp = exp;
    }

    @Override
    public String toTrue() {
        return String.format("not (%1$s)", exp.toFalse());
    }

    @Override
    public String toFalse() {
        return String.format("not (%1$s)", exp.toTrue());
    }

    @Override
    public String toNull() {
        return String.format("%1$s", exp.toNull());
    }

    @Override
    public String toExec() {
        return String.format("not (%1$s)", exp.toExec());
    }

    @Override
    public String toString() {
        return String.format("NOT %1$s", exp.toString());
    }
}
