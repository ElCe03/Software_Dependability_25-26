package controllers;

import java.time.LocalDate;

public class FakeDatePicker {
    private LocalDate date;

    public FakeDatePicker(LocalDate d) {
        this.date = d;
    }

    public LocalDate getValue() {
        return date;
    }

    public void setValue(LocalDate d) {
        this.date = d;
    }
}
