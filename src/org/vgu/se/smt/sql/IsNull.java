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

public class IsNull implements Expression {
    private Expression exp;
    final String TRUE = "(= %1$s %2$s)";
    final String FALSE = "(not (= %1$s %2$s))";

    @Override
    public String toTrue() {
        if (exp instanceof LongValue) {
            return String.format(TRUE, exp.toExec(), "nullInteger");
        }
        return null;
    }

    @Override
    public String toFalse() {
        if (exp instanceof LongValue) {
            return String.format(FALSE, exp.toExec(), "nullInteger");
        }
        return null;
    }

    @Override
    public String toNull() {
        return "false";
    }

    @Override
    public String toExec() {
        // TODO Auto-generated method stub
        return null;
    }

    public Expression getExp() {
        return exp;
    }

    public void setExp(Expression exp) {
        this.exp = exp;
    }
    

    @Override
    public String toString() {
        return String.format("%1$s IS NULL", exp.toString());
    }
}
