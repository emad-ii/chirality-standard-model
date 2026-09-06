import { lazy, Suspense, useState, useRef } from 'react';
import { fireEvent, render, screen } from '@testing-library/react';
import { expect, it, vi } from 'vitest';
import { ExhibitBoundary } from '@/components/exhibit-boundary';

it('contains a rejected optional import and preserves the surrounding selection', async () => {
  const error = vi.spyOn(console, 'error').mockImplementation(() => {});
  const Missing = lazy(() => Promise.reject(new Error('chunk unavailable')));
  function Exhibit() {
    const [cell, setCell] = useState(2);
    const [flat, setFlat] = useState(false);
    const flatViewControl = useRef<HTMLButtonElement>(null);
    return (
      <>
        <button onClick={() => setCell(4)}>Select cell four</button>
        <output aria-label="Cell">{cell}</output>
        <button ref={flatViewControl} onClick={() => setFlat(true)}>
          The flat view
        </button>
        {flat ? (
          <p>Flat projection of cell {cell}</p>
        ) : (
          <ExhibitBoundary
            onFlatView={() => setFlat(true)}
            flatViewControl={flatViewControl}
          >
            <Suspense fallback={<p>Loading</p>}>
              <Missing />
            </Suspense>
          </ExhibitBoundary>
        )}
      </>
    );
  }
  render(<Exhibit />);
  await screen.findByText(/3D could not load/);
  expect(error).toHaveBeenCalled();
  fireEvent.click(screen.getByRole('button', { name: 'Select cell four' }));
  expect(screen.getByLabelText('Cell').textContent).toBe('4');
  fireEvent.click(screen.getByRole('button', { name: 'Use the flat view' }));
  expect(screen.getByText('Flat projection of cell 4')).toBeTruthy();
  expect(document.activeElement).toBe(
    screen.getByRole('button', { name: 'The flat view' }),
  );
});
