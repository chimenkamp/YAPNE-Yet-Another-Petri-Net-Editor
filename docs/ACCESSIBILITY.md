# WCAG 2.0 Accessibility Implementation

##### Navigation
- `Tab` / `Shift+Tab` - Navigate through elements on canvas
- `Arrow Keys` - Move focused element (hold Shift for fine control 1px steps)
- `Enter` - Select/activate focused element
- `Escape` - Clear selection

##### Tools (Alt + Key)
- `Alt+P` - Add Place tool
- `Alt+T` - Add Transition tool
- `Alt+A` - Add Arc tool
- `Alt+S` - Select tool

##### Actions
- `Space` - Fire focused transition (when enabled)
- `Delete` / `Backspace` - Delete focused element
- `I` - Increment tokens on focused place
- `D` - Decrement tokens on focused place
- `Ctrl/Cmd+R` - Run simulation step

##### View Controls
- `Ctrl/Cmd +` - Zoom in
- `Ctrl/Cmd -` - Zoom out
- `Ctrl/Cmd 0` - Reset zoom to 100%

##### Help
- `?` or `H` - Show keyboard shortcuts and accessibility help

#### 2.2 No Keyboard Traps
- All modal dialogs can be closed with `Escape`
- Focus properly managed in all interactions
- Tab order is logical and predictable

#### 2.3 Focus Indicators
- **Visible Focus**: 3px solid outline with 3:1 contrast ratio
- **Keyboard Mode Indicator**: Enhanced focus when using keyboard
- **Canvas Focus**: Visual indicator on canvas elements being navigated

#### 2.4 Skip Links
- Skip to canvas
- Skip to properties
- Skip to tools

### 3. Understandable (WCAG Principle 3)

#### 3.1 Language
- `lang="en"` attribute set on HTML
- Clear, concise labels and instructions

#### 3.2 Predictable
- Consistent navigation and behavior
- No unexpected context changes
- Logical tab order

#### 3.3 Input Assistance
- All form controls have labels
- Error messages are clear and associated with controls
- Help text available via `?` key

### 4. Robust (WCAG Principle 4)

#### 4.1 Compatible
- Valid HTML5
- Proper ARIA roles and states
- Works with major screen readers (NVDA, JAWS, VoiceOver)

#### 4.2 ARIA Implementation
- `role="application"` for canvas area
- `aria-label` on all interactive elements
- `aria-live` regions for announcements
- `aria-describedby` for complex elements

## Using the Accessibility Features

### Accessibility Menu

Click the **♿ Accessibility** button in the top-right corner to access:

1. **High Contrast Mode** - Enhanced visual contrast for low vision users
2. **Enhanced Screen Reader Mode** - Additional announcements and descriptions
3. **Show Keyboard Hints** - Visual keyboard shortcut indicators
4. **View Keyboard Shortcuts** - Complete list of keyboard commands
5. **Describe Canvas Content** - Hear a summary of the Petri net

### Screen Reader Support

The editor provides comprehensive screen reader support:

- **Element Navigation**: Tab through places, transitions, and arcs
- **State Announcements**: Hear when elements are selected, moved, or modified
- **Simulation Feedback**: Announcements when transitions fire
- **Live Updates**: Changes to token counts and network state are announced

### Keyboard-Only Operation

Every feature is accessible via keyboard:

1. **Navigate**: Use Tab to move between canvas elements
2. **Move Elements**: Use Arrow keys to position elements
3. **Add Elements**: Use Alt+P/T/A shortcuts to activate tools
4. **Simulate**: Use Space to fire transitions, Ctrl+R for step
5. **Edit**: Use I/D to modify tokens, Delete to remove elements

### High Contrast Mode

Optimized for users with low vision or color blindness:

- Black background with white elements
- Yellow highlights for important states
- Increased contrast ratios
- Simplified color palette

## Testing Accessibility

### Keyboard Navigation Test
1. Load the editor
2. Press Tab to navigate through interface
3. Use Arrow keys to navigate canvas elements
4. Verify all functionality accessible via keyboard

### Screen Reader Test
1. Enable NVDA, JAWS, or VoiceOver
2. Navigate to editor
3. Tab through elements
4. Verify announcements are clear and accurate

### Color Contrast Test
All text and UI elements have been verified to meet WCAG AA requirements:
- Normal text: 4.5:1 minimum
- Large text: 3:1 minimum
- UI components: 3:1 minimum

### Focus Indicator Test
1. Tab through all interactive elements
2. Verify focus indicators are clearly visible
3. Check that focus indicators have 3:1 contrast with background

## Browser Compatibility

Tested and verified in:
- Chrome 90+
- Firefox 88+
- Safari 14+
- Edge 90+

## Assistive Technology Compatibility

Tested with:
- **NVDA** (Windows)
- **JAWS** (Windows)
- **VoiceOver** (macOS/iOS)
- **TalkBack** (Android)

## WCAG 2.0 Compliance Checklist

### Level A
- ✅ 1.1.1 Non-text Content
- ✅ 1.2.1 Audio-only and Video-only (N/A)
- ✅ 1.3.1 Info and Relationships
- ✅ 1.3.2 Meaningful Sequence
- ✅ 1.3.3 Sensory Characteristics
- ✅ 1.4.1 Use of Color
- ✅ 1.4.2 Audio Control (N/A)
- ✅ 2.1.1 Keyboard
- ✅ 2.1.2 No Keyboard Trap
- ✅ 2.2.1 Timing Adjustable (N/A)
- ✅ 2.2.2 Pause, Stop, Hide
- ✅ 2.3.1 Three Flashes
- ✅ 2.4.1 Bypass Blocks
- ✅ 2.4.2 Page Titled
- ✅ 2.4.3 Focus Order
- ✅ 2.4.4 Link Purpose
- ✅ 3.1.1 Language of Page
- ✅ 3.2.1 On Focus
- ✅ 3.2.2 On Input
- ✅ 3.3.1 Error Identification
- ✅ 3.3.2 Labels or Instructions
- ✅ 4.1.1 Parsing
- ✅ 4.1.2 Name, Role, Value

### Level AA
- ✅ 1.2.4 Captions (Live) (N/A)
- ✅ 1.2.5 Audio Description (N/A)
- ✅ 1.4.3 Contrast (Minimum)
- ✅ 1.4.4 Resize Text
- ✅ 1.4.5 Images of Text
- ✅ 2.4.5 Multiple Ways
- ✅ 2.4.6 Headings and Labels
- ✅ 2.4.7 Focus Visible
- ✅ 3.1.2 Language of Parts
- ✅ 3.2.3 Consistent Navigation
- ✅ 3.2.4 Consistent Identification
- ✅ 3.3.3 Error Suggestion
- ✅ 3.3.4 Error Prevention
- ✅ 4.1.3 Status Messages

## Implementation Details

### Canvas Accessibility Architecture

The accessibility layer uses multiple strategies:

1. **Virtual DOM Mirror**: An invisible DOM tree mirrors canvas elements
2. **Focus Management**: Keyboard focus tracked separately from mouse
3. **ARIA Live Regions**: Polite and assertive regions for announcements
4. **Keyboard Event Handlers**: Comprehensive keyboard navigation
5. **Visual Focus Indicators**: Canvas elements show focus state

### Code Structure

```
src/accessibility/
  ├── wcag-canvas-accessibility.js  # Main accessibility layer
  └── accessibility-integration.js   # Integration with app

styles/
  └── accessibility.css              # Accessibility-specific styles
```

## Future Enhancements

Potential improvements for AAA compliance:
- Enhanced keyboard navigation with spatial modes
- Audio cues for state changes
- Extended color customization
- Voice control integration
- Gesture alternatives for touch devices

## Reporting Accessibility Issues

If you encounter any accessibility barriers, please report them via:
- GitHub Issues
- Email: accessibility@yapne.org

Please include:
- Browser and version
- Assistive technology (if applicable)
- Steps to reproduce
- Expected vs actual behavior

## Resources

- [WCAG 2.0 Guidelines](https://www.w3.org/WAI/WCAG20/quickref/)
- [WAI-ARIA Authoring Practices](https://www.w3.org/WAI/ARIA/apg/)
- [Canvas Accessibility Guide](https://www.w3.org/WAI/WCAG21/Techniques/html/H91)

## License

This accessibility implementation is part of YAPNE and shares the same license.

---

**Last Updated**: October 24, 2025  
**WCAG Version**: 2.0 Level AA  
**Status**: Fully Compliant ✅
