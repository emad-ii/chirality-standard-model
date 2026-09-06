'use client';
import { Component, type ReactNode, type RefObject } from 'react';
import { Button } from '@/components/ui/button';

/** A failed optional chunk must not remove the surrounding argument or controls. */
export class ExhibitBoundary extends Component<
  {
    children: ReactNode;
    onFlatView: () => void;
    flatViewControl: RefObject<HTMLButtonElement | null>;
  },
  { failed: boolean }
> {
  state = { failed: false };
  static getDerivedStateFromError() {
    return { failed: true };
  }
  render() {
    if (!this.state.failed) return this.props.children;
    return (
      <div className="webgl-fallback">
        <output>
          3D could not load. The flat projection and numerical checks are still
          available.
        </output>
        <Button
          variant="outline"
          onClick={() => {
            this.props.onFlatView();
            this.props.flatViewControl.current?.focus();
          }}
        >
          Use the flat view
        </Button>
      </div>
    );
  }
}
