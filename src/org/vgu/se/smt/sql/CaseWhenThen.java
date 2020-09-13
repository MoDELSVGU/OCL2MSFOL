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

public class CaseWhenThen implements Expression {
    private Expression caze;
    private Expression when;
    private Expression elze;
    final String TRUE = "(and (=> %1$s %2$s)\r\n" + "     (=> %3$s %4$s)\r\n"
        + "     (=> %5$s %6$s)\r\n";
    final String FALSE = "(and (=> %1$s %2$s)\r\n" + "     (=> %3$s %4$s)\r\n"
        + "     (=> %5$s %6$s)\r\n";
    final String NULL = "(and (=> %1$s %2$s)\r\n" + "     (=> %3$s %4$s)\r\n"
        + "     (=> %5$s %6$s)\r\n";

    public Expression getCaze() {
        return caze;
    }

    public void setCaze(Expression caze) {
        this.caze = caze;
    }

    public Expression getWhen() {
        return when;
    }

    public void setWhen(Expression when) {
        this.when = when;
    }

    public Expression getElze() {
        return elze;
    }

    public void setElze(Expression elze) {
        this.elze = elze;
    }

    @Override
    public String toTrue() {
        return String.format(TRUE, caze.toTrue(), when.toTrue(), caze.toFalse(),
            elze.toTrue(), caze.toNull(), elze.toTrue());
    }

    @Override
    public String toFalse() {
        return String.format(FALSE, caze.toTrue(), when.toFalse(),
            caze.toFalse(), elze.toFalse(), caze.toNull(), elze.toFalse());
    }

    @Override
    public String toNull() {
        return String.format(TRUE, caze.toTrue(), when.toNull(), caze.toFalse(),
            elze.toNull(), caze.toNull(), elze.toNull());
    }

    @Override
    public String toExec() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public String toString() {
        return String.format("CASE WHEN %1$s THEN %2$s ELSE %3$s",
            caze.toString(), when.toString(), elze.toString());
    }

}
